-- Prove2me | Theorems.Thm_SmaleNinth_smale_ninth_no_linear_time
-- name    : SmaleNinth.smale_ninth_no_linear_time
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-07T18:36:54.491867+00:00
-- url     : https://prove2.me/theorems/30fa940c-23d0-40db-b9d7-b6e5239745cc
-- title:
--   Smale's ninth problem: no linear-time program
-- statement:
--   The mission's goal asserts the existence of a program $P$ and constants $C, d$ such that $P$ decides $\{x \mid Ax \ge b\} \ne \emptyset$ within $C\,(mn+m+2)^d$ steps for all $m$, $n$, $A$, $b$. This statement settles the case $d = 1$ negatively.
--
--   **The assertion.** For every program $P$ in the fixed instruction set of the mission's machine and every constant $C$, there are $m$, $n$, $A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$ such that $P$, started on the standard encoding, does not halt with the correct verdict within $C\,(mn+m+2)$ steps.
--
--   **Reading.** The exponent $d$ in the goal is genuinely needed: no algorithm in this model runs in time linear in the number of input reals. The reason is the fixed-address structure of the machine: a single-variable instance places each coefficient $a_i$ exactly $m$ cells away from its right-hand side $b_i$, and the one-variable lower bound shows that a linear budget leaves too few boundary crossings to combine them. Taking $n = 1$, the input size is $2m + 2$, so a linear budget $C(mn+m+2)$ is a linear budget $2C(m+1)$ for the one-variable problem, which is excluded.
--
--   **What it leaves open.** Everything with $d \ge 2$. The mission's goal is the assertion that some $d$ works; this theorem only shows that $d = 1$ does not.
-- source:
--   Corollary of SmaleNinth.bss_one_variable_lp_no_linear_program (crossing-sequence lower bound, cf. Hennie 1965, Information and Control 8, 553-578) applied to the n = 1 instances of the goal theorem SmaleNinth.smale_ninth_problem of the mission Smale's Ninth Problem.

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine

/-!
The goal statement of the mission with the exponent fixed to `d = 1` is
false: no uniform program decides LP feasibility within a bound linear in
the input size `mn + m + 2`.

Source: corollary of the one-variable lower bound
`SmaleNinth.bss_one_variable_lp_no_linear_program` (crossing-sequence
argument for fixed-address real machines): the instances with `n = 1` have
input size `2m + 2`, so a linear budget for the goal is a linear budget for
the one-variable problem.
-/

open Matrix LinearOptimization

/-- **Smale's ninth problem, degree-one exclusion.** For every program `P`
and constant `C`, `P` does not decide LP feasibility within `C·(mn+m+2)`
steps on all instances. -/

theorem SmaleNinth.smale_ninth_no_linear_time (P : BSSProgram) (C : ℕ) :
    ¬ ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          BSSDecidesInTime P (encodeLP A b) (C * (m * n + m + 2)) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) := by sorry
