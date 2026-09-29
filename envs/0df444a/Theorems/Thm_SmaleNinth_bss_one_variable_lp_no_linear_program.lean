-- Prove2me | Theorems.Thm_SmaleNinth_bss_one_variable_lp_no_linear_program
-- name    : SmaleNinth.bss_one_variable_lp_no_linear_program
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-07T18:34:13.934361+00:00
-- url     : https://prove2.me/theorems/6c7fd385-59e7-4a79-91b0-092c16431180
-- title:
--   No linear-time BSS program for one-variable LP feasibility
-- statement:
--   This is the negative form of the one-variable model-sanity statement: in the machine model of the mission, a fixed program cannot decide one-variable linear feasibility in time linear in the number of constraints.
--
--   **The assertion.** For every program $P$ over the reals in the fixed instruction set (real constants, field arithmetic at fixed addresses, two-sided tape shifts, a sign-test branch) and every constant $C$, there exist $m$ and a one-variable system $a_i x \ge b_i$ ($i = 1, \dots, m$) such that $P$, started on the standard encoding, does **not** halt with the correct verdict within $C(m+1)$ steps.
--
--   **Why.** Every instruction addresses cells at fixed offsets from the head, so a program is a window of fixed width $2W+1$ sliding along the tape one cell per shift. The coefficient $a_i$ and the right-hand side $b_i$ sit $m$ cells apart. In $C(m+1)$ steps some boundary between the two blocks is crossed at most $C+1$ times, so the computation is determined across that boundary by the window contents at those crossings, a transcript of at most $(C+1)(2W+1)$ real numbers. On corner instances (coefficients $x \in \mathbb{R}^p$ and right-hand sides equal to $x$, plus a sentinel constraint $x \le 1$) equal transcripts allow cutting and pasting the two runs into the mixed instance $(x, x')$, which must then be declared feasible, forcing $x' \le x$ and symmetrically $x = x'$. Hence the transcript is injective on an open subset of $\mathbb{R}^p$ with $p > (C+1)(2W+1)$; but near a generic input the transcript is a $C^1$ function of the input, and a $C^1$ map into a space of smaller dimension is injective on no open set.
--
--   **Context.** The quadratic budget $C(m+1)^2$ is attainable (`SmaleNinth.bss_decides_one_variable_lp_quadratic`), so this theorem pins the complexity of the one-variable problem in this model at $\Theta(m^2)$. It is the positive-statement form of the disproof of `SmaleNinth.bss_decides_one_variable_lp`, published so that other lower bounds can import it.
-- source:
--   Crossing-sequence lower bound for one-tape machines (Hennie 1965, Information and Control 8, 553-578), adapted to the BSS-style machine of Definitions.Def_SmaleNinth_BSSMachine; formal content identical to the accepted disproof of SmaleNinth.bss_decides_one_variable_lp (mission Smale's Ninth Problem).

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine

/-!
A lower bound in the Blum–Shub–Smale machine of
`Definitions.Def_SmaleNinth_BSSMachine`: no uniform program decides
one-variable LP feasibility in linear time.

Source: crossing-sequence argument for one-tape machines (F. C. Hennie,
*One-tape, off-line Turing machine computations*, Information and Control
8 (1965) 553–578) adapted to real-number machines with fixed-address
instructions; the algebraic step is a dimension argument (a `C¹` map from an
open subset of `ℝ^p` into `ℝ^q`, `q < p`, is not injective). Formal proof:
the accepted disproof of `SmaleNinth.bss_decides_one_variable_lp`.
-/

open Matrix LinearOptimization

/-- **Linear-time lower bound for one-variable LP feasibility.** For every
program `P` and constant `C` there is a one-variable instance that `P` does
not decide correctly within `C·(m+1)` steps. -/

theorem SmaleNinth.bss_one_variable_lp_no_linear_program (P : BSSProgram) (C : ℕ) :
    ¬ ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          BSSDecidesInTime P (encodeLP A b) (C * (m + 1)) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) := by sorry
