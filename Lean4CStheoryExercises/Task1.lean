/- Copyright (c) Kelin Luo, 2026.  All rights reserved. -/

-- Instructions for Lean Task Project
-- 1. Coding Environment
--     * Complete this task in the checked-out Lean4CStheory-Exercises project.
--     * Open this file in VS Code using the Lean extension.
--     * You may use Lean Online for small standalone experiments, but the complete
--       task depends on project-local definitions and must compile in this project.
--     * Submit a single Lean file that compiles without errors.
-- 2. Learning Resources
--     * Official Lean documentation:
--       https://leanprover-community.github.io/learn.html
--       https://leanprover-community.github.io/mathematics_in_lean/
-- 3. Use of AI Tools
--     * You may use AI tools (ChatGPT, GitHub Copilot, etc.) to:
--         - understand Lean syntax
--         - understand tactics
--         - debug errors
--         - explain examples
--     * If AI tools are used, you must include the prompts as comments
--       starting with:  -- Prompt:
-- 4. Submission Format
--     * The file must be clean, readable, and well-commented.
--     * Your own solutions must be clearly distinguishable from AI references.

import Lean4CStheoryExercises.Init
import Mathlib.Data.Real.Basic

namespace Lean4CStheoryExercises.Task1

/-!
# Task 1

This task begins with elementary arithmetic, asymptotic notation, and
structural induction. It then moves to short graph and algorithm exercises
that practice the same basic Lean proof patterns in concrete settings.
-/

/-!
## Part I: Asymptotics Exercises

Start with these exercises. They progress from familiar arithmetic to simple
asymptotic definitions and induction.
-/

/-!
=====================================
Lean Tactics Reference
=====================================

The following tactics are used throughout this task:

* rw        : rewrite a goal or hypothesis using an equality
* simp      : simplify expressions using rewrite rules
* calc      : structure multi-step equalities or inequalities
* linarith  : solve linear arithmetic goals and inequalities
* nlinarith : solve nonlinear arithmetic goals
* ring      : normalize algebraic expressions involving addition and multiplication
* constructor : split goals of the form A ∧ B
* intro     : introduce universally quantified variables or assumptions
* norm_num  : evaluate numeric expressions and close simple arithmetic goals
* induction : prove statements about recursively defined objects (e.g., ℕ)

You are expected to understand how and why these tactics are applied in the examples
and exercises, and to follow similar proof patterns in your own solutions.
-/

section basics
/-!
### Section 0: Math Basics (4 points)
This section focuses on equations and inequalities.
Follow the structure of the examples when solving the exercises.
-/

-- Example 0.1
example {a b : ℝ} (h1 : a = 3) (h2 : b = -1) : a + b = 2 :=
  calc
    a + b = 3 + b := by rw [h1]
    _ = 3 + (-1) := by rw [h2]
    _ = -1 + 3 := by rw [add_comm]
    _ = 2 := by norm_num

-- (1 point) Exercise 0.1
@[exercise "0.1" 1]
theorem exercise_0_1 {a b : ℝ} (h1 : a = 3) (h2 : b = 4) : a + 2 * b = 11 :=
  calc
  a + 2 * b = 3 + 2 * b := by rw [h1]
  _ = 3 + 2 * 4 := by rw [h2]
  _ = 11 := by norm_num

-- Example 0.2
example {n : ℕ} (h1 : c = 1) : 2 * n + 10 ≥ c * 2 := by
  rw [h1]
  simp

-- (1 point) Exercise 0.2
@[exercise "0.2" 1]
theorem exercise_0_2 {n : ℕ} (h1 : c = 3) : 5 * n + 6 ≥ c := by
  rw [h1]
  simp

-- Example 0.3
example {n : ℕ} (h1 : c = 5) : 4 * n ≤ c * n := by
  rw [h1]
  calc
    4 * n ≤ 5 * n := by
      have h : 0 ≤ n := Nat.zero_le n
      linarith

-- Example 0.3 (alternative proof)
example {n : ℕ} (h1 : c = 5) : 4 * n ≤ c * n := by
  rw [h1]
  linarith

-- (1 point) Exercise 0.3
@[exercise "0.3" 1]
theorem exercise_0_3 {n : ℕ} (h1 : c = 2) : 4 * n + 3 ≥ c * (n + 1) := by
  rw [h1]
  calc
    4 * n + 3 ≥ 2 * (n + 1) := by
      have h : 0 ≤ n := Nat.zero_le n
      linarith

-- Example 0.4
example {n : ℕ} (h1 : n ≥ 1) (h2 : c = 1) :
  12 * n^2 ≥ c * (2 * n + 10) := by
  calc
    12 * n^2 = 12 * n * n := by ring
    _ ≥ 2 * n + 10 := by nlinarith
    _ = c * (2 * n + 10) := by rw [h2]; ring

-- Example 0.5
example {n : ℕ} (h1 : n ≥ 2) (h2 : c₁ = 1) (h3 : c₂ = 4) :
  c₁ * n ≤ 2 * n + 5 ∧ n + 1 ≤ c₂ * n := by
  rw [h2, h3]
  constructor
  · linarith [h1]
  · linarith [h1]

-- (1 point) Exercise 0.4
@[exercise "0.4" 1]
theorem exercise_0_4 {n : ℕ} (h1 : n ≥ 10) (h2 : c₁ = 1) (h3 : c₂ = 10) :
  c₁ * (2 * n + 1) ≤ 5 * n ∧ 5 * n ≤ c₂ * (2 * n + 1) := by
  rw [h2, h3]
  constructor
  . linarith [h1]
  . linarith [h1]

end basics

section asymptotics
/-!
### Section 1: Asymptotic Analysis in Lean (5 points)
This section introduces Big-O, Big-Omega, and Big-Theta.
You are expected to follow the definitions exactly.
-/

-- Definition of Big-O
def isBigO (f g : ℕ → ℝ) : Prop :=
  ∃ (c n₀ : ℝ), 0 < c ∧ ∀ n : ℕ, n ≥ n₀ → f n ≤ c * g n

-- (1 point) Exercise 1.1
-- Define Big-Omega using the same style as Big-O.
@[exercise "1.1" 1]
def isBigOmega (f g : ℕ → ℝ) : Prop :=
  ∃ (c n₀ : ℝ), 0 < c ∧ ∀ n : ℕ, n ≥ n₀ → f n ≥ c * g n

-- (1 point) Exercise 1.2
-- Define Big-Theta using Big-O and Big-Omega.
@[exercise "1.2" 1]
def isBigTheta (f g : ℕ → ℝ) : Prop :=
  isBigO f g ∧ isBigOmega f g

-- Example 1.2
example : isBigO (fun n ↦ (2 : ℝ) * n + 4) (fun n ↦ n) := by
  use 3, 4
  constructor
  · linarith
  intro n hn
  calc
    (2 : ℝ) * n + 4 ≤ 2 * n + n := by linarith [hn]
    _ = 3 * n := by ring

-- (1 point) Exercise 1.3
@[exercise "1.3" 1]
theorem exercise_1_3 : isBigO (fun n ↦ (3 : ℝ) * n + 2) (fun n ↦ n) := by
  use 4, 2
  constructor
  . linarith
  intro n hn
  calc
    (3 : ℝ) * n + 2 ≤ 3 * n + n := by linarith [hn]
    _ = 4 * n := by ring

-- (1 point) Exercise 1.4
@[exercise "1.4" 1]
theorem exercise_1_4 : isBigOmega (fun n ↦ (3 : ℝ) * n + 2) (fun n ↦ n) := by
  use 1, 4
  constructor
  . linarith
  intro n hn
  calc
    (3 : ℝ) * n + 2 ≤ 3 * n + n := by linarith [hn]
    _ = 5 * n := by ring


-- (1 point) Exercise 1.5
@[exercise "1.5" 1]
theorem exercise_1_5 : isBigTheta (fun n ↦ (3 : ℝ) * n + 2) (fun n ↦ n) := by
  use 2, 4
  constructor
  . linarith
  intro n hn
  calc
    (3 : ℝ) * n + 2 ≥ 3 * n + n := by linarith [hn]
    _ = 2 * n := by ring

end asymptotics

section recursion
/-!
### Section 2: Recursion and Induction (3 points)
Only structural recursion is permitted.
Do not use subtraction-based recursion.
-/

-- Example 2.1
def sumNR : ℕ → ℝ
  | 0     => 0
  | n + 1 => sumNR n + (n + 1)

example (n : ℕ) : sumNR n = n * (n + 1) / 2 := by
  induction n with
  | zero =>
      simp [sumNR]
  | succ k IH =>
      simp [sumNR, IH]
      ring

-- (2 points) Exercise 2.1
def sumOdd : ℕ → ℕ
  | 0     => 1
  | n + 1 => sumOdd n + (2 * (n + 1) + 1)

@[exercise "2.1" 2]
theorem exercise_2_1 (n : ℕ) : sumOdd n = (n + 1) ^ 2 := by
  induction n with
  | zero =>
      simp[sumOdd]
  | succ k IH =>
      simp [sumOdd, IH]
      ring

-- (1 point) Exercise 2.2
-- Define the Fibonacci function fib(n).
-- Only the function definition is required.
@[exercise "2.2" 1]
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

end recursion

/-!
## Part II: Algorithm Warmup Exercises

These exercises use tiny graph models to practice reading
definitions and filling in one, two, or three small proof steps.

Useful tactics in this part:

* `norm_num` checks simple number facts.
* `left` and `right` choose a side of an "or" statement.
* `constructor` splits an "and" statement into two goals.
* `exact h` closes a goal using a hypothesis named `h`.
* `use x` gives an example object when the goal says "there exists".
* `rw [h]` rewrites using an equality named `h`.
-/

section graph_basics
/-!
### Section 3: Graph Basics

Tiny map:

0 -- 1 -- 2 -- 3
-/

def Road (u v : Nat) : Prop :=
  (u = 0 ∧ v = 1) ∨
  (u = 1 ∧ v = 2) ∨
  (u = 2 ∧ v = 3)

def TwoHopWalk (u w : Nat) : Prop :=
  ∃ middle : Nat, Road u middle ∧ Road middle w

-- Example 3.1
example : Road 0 1 := by
  left
  constructor
  · norm_num
  · norm_num

-- (1 point) Exercise 3.1
@[exercise "3.1" 1]
theorem exercise_3_1 : Road 1 2 := by
  right
  left
  constructor
  · norm_num
  · norm_num

-- Example 3.2
example : TwoHopWalk 0 2 := by
  use 1
  constructor
  · left
    constructor
    · norm_num
    · norm_num
  · right
    left
    constructor
    · norm_num
    · norm_num

-- (1 point) Exercise 3.2
@[exercise "3.2" 1]
theorem exercise_3_2 : TwoHopWalk 1 3 := by
  use 2
  constructor
  · right
    left
    constructor
    . norm_num
    . norm_num
  . right
    right
    constructor
    . norm_num
    . norm_num

end graph_basics

section bipartite
/-!
### Section 4: Bipartite Test

Color the tiny map by alternating colors:

vertex 0: red
vertex 1: blue
vertex 2: red
vertex 3: blue
-/

def Color : Nat -> Bool
  | 0 => false
  | 1 => true
  | 2 => false
  | 3 => true
  | _ => false

def DifferentColors (u v : Nat) : Prop :=
  Color u ≠ Color v

-- Example 4.1
example : DifferentColors 0 1 := by
  norm_num [DifferentColors, Color]

-- (1 point) Exercise 4.1
@[exercise "4.1" 1]
theorem exercise_4_1 : DifferentColors 1 2 := by
  norm_num [DifferentColors, Color]

-- Example 4.2
example : Road 0 1 ∧ DifferentColors 0 1 := by
  constructor
  · left
    constructor
    · norm_num
    · norm_num
  · norm_num [DifferentColors, Color]

-- (1 point) Exercise 4.2
@[exercise "4.2" 1]
theorem exercise_4_2 : Road 1 2 ∧ DifferentColors 1 2 := by
  constructor
  · right
    constructor
    . norm_num
  . norm_num [DifferentColors, Color]

end bipartite

section bfs
/-!
### Section 5: BFS

BFS starts at vertex 0.

level 0: vertex 0
level 1: vertices 1 and 2
level 2: vertex 3
-/

def BfsLevel : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | _ => 0

def InBfsLayer (v layer : Nat) : Prop :=
  BfsLevel v = layer

-- Example 5.1
example : InBfsLayer 1 1 := by
  norm_num [InBfsLayer, BfsLevel]

-- (1 point) Exercise 5.1
@[exercise "5.1" 1]
theorem exercise_5_1 : InBfsLayer 3 2 := by
  norm_num [InBfsLayer, BfsLevel]

-- Example 5.2
example : InBfsLayer 1 1 ∧ InBfsLayer 2 1 := by
  constructor
  · norm_num [InBfsLayer, BfsLevel]
  · norm_num [InBfsLayer, BfsLevel]

-- (1 point) Exercise 5.2
@[exercise "5.2" 1]
theorem exercise_5_2 : InBfsLayer 0 0 ∧ InBfsLayer 3 2 := by
  constructor
  · norm_num [InBfsLayer, BfsLevel]
  · norm_num [InBfsLayer, BfsLevel]

-- Example 5.3
example : Road 0 1 ∧ InBfsLayer 1 1 := by
  constructor
  · left
    constructor
    · norm_num
    · norm_num
  · norm_num [InBfsLayer, BfsLevel]

-- (1 point) Exercise 5.3
@[exercise "5.3" 1]
theorem exercise_5_3 : Road 1 2 ∧ InBfsLayer 2 1 := by
  constructor
  · right
    constructor
    . norm_num
  . norm_num [InBfsLayer, BfsLevel]

end bfs

section dfs
/-!
### Section 6: DFS

In this tiny DFS tree, vertex 0 is the start.

parent of 1 is 0
parent of 2 is 1
parent of 3 is 1
-/

def DfsParent : Nat -> Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | _ => 0

def DfsTime : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0

def IsDfsChild (parent child : Nat) : Prop :=
  DfsParent child = parent

-- Example 6.1
example : IsDfsChild 0 1 := by
  norm_num [IsDfsChild, DfsParent]

-- (1 point) Exercise 6.1
@[exercise "6.1" 1]
theorem exercise_6_1 : IsDfsChild 1 2 := by
  norm_num [IsDfsChild, DfsParent]

-- Example 6.2
example : DfsTime 0 < DfsTime 1 := by
  norm_num [DfsTime]

-- (1 point) Exercise 6.2
@[exercise "6.2" 1]
theorem exercise_6_2 : DfsTime 1 < DfsTime 3 := by
  norm_num [DfsTime]

-- Example 6.3
example : DfsTime 0 < DfsTime 2 := by
  have h01 : DfsTime 0 < DfsTime 1 := by
    norm_num [DfsTime]
  have h12 : DfsTime 1 < DfsTime 2 := by
    norm_num [DfsTime]
  exact Nat.lt_trans h01 h12

-- (1 point) Exercise 6.3
@[exercise "6.3" 1]
theorem exercise_6_3 : DfsTime 0 < DfsTime 3 := by
  have h01 : DfsTime 0 < DfsTime 1 := by
    norm_num [DfsTime]
  have h13 : DfsTime 1 < DfsTime 3 := by
    norm_num [DfsTime]
  exact Nat.lt_trans h01 h13

end dfs

end Lean4CStheoryExercises.Task1
