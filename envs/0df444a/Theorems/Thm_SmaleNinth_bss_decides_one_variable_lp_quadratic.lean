-- Prove2me | Theorems.Thm_SmaleNinth_bss_decides_one_variable_lp_quadratic
-- name    : SmaleNinth.bss_decides_one_variable_lp_quadratic
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-07T17:24:35.644642+00:00
-- url     : https://prove2.me/theorems/08c79518-19a2-4dc9-83e9-1d3eb405a99e
-- title:
--   Model sanity: one-variable LP in quadratic BSS time
-- statement:
--   This statement calibrates the machine model of the mission's goal by exhibiting a genuine uniform algorithm in it, in the smallest nontrivial case, with a *quadratic* time budget.
--
--   **The assertion.** There exist a single program $P$ over the real numbers and a single constant $C \in \mathbb{N}$ such that for every $m$ and every one-variable system given by $a \in \mathbb{R}^m$ and $b \in \mathbb{R}^m$, the program started on the standard tape encoding (cells $0,1$ hold $m$ and $1$, cells $2,\dots,m+1$ hold $a$, cells $m+2,\dots,2m+1$ hold $b$) halts within
--
--   $$C\,(m+1)^2 \text{ steps}$$
--
--   with the verdict true if and only if $\{\,x \in \mathbb{R} \mid a_i x \ge b_i \text{ for } i = 1,\dots,m\,\}$ is nonempty.
--
--   **Reading the quantifiers.** The program and the constant are fixed once and serve every instance: the algorithm is uniform, and its cost is a fixed polynomial in the number of constraints with a constant independent of the data. When $m = 0$ the system is vacuously satisfiable and the program must accept within $C$ steps.
--
--   **Why quadratic.** In this machine every instruction addresses fixed tape cells and the only way to reach other cells is to shift the whole tape by one position. The coefficient $a_i$ and the right-hand side $b_i$ sit $m$ cells apart, so combining them requires walking the head across the gap while carrying the running bounds along in a fixed window of register cells; one round trip per constraint costs $\Theta(m)$ instructions, and $m$ constraints cost $\Theta(m^2)$. The mathematics is the interval characterisation of one-variable feasibility: the system is solvable iff no row has $a_i = 0 < b_i$ and $\max_{a_i > 0} b_i/a_i \le \min_{a_j < 0} b_j/a_j$.
--
--   **Relation to the milestone.** This is the mission's model-sanity milestone `bss_decides_one_variable_lp` with the linear budget $C(m+1)$ replaced by $C(m+1)^2$. The linear budget appears to be unattainable in the fixed-address model, by a crossing-sequence argument (see the mission discussion), whereas the quadratic budget is achieved by an explicit program.
-- source:
--   Model-validation exercise for the BSS machine of Blum-Shub-Smale, Bull. AMS 21(1):1-46, 1989, Section 1; quadratic-time form of the mission milestone SmaleNinth.bss_decides_one_variable_lp (mission Smale's Ninth Problem). The underlying mathematics is the interval characterization of one-variable linear feasibility (Fourier-Motzkin base case).

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine

/-!
Model sanity for the Blum–Shub–Smale machine of
`Definitions.Def_SmaleNinth_BSSMachine`, quadratic-time form: a single uniform
program decides one-variable LP feasibility within `C·(m+1)²` steps.

Source: model-validation exercise for the BSS machine (Blum–Shub–Smale,
Bull. AMS 21(1):1–46, 1989, Section 1). The mathematics is the interval
characterisation of one-variable feasibility: `aᵢx ≥ bᵢ (i = 1,…,m)` is
solvable iff no row has `aᵢ = 0 < bᵢ` and the largest lower bound `bᵢ/aᵢ`
over `aᵢ > 0` is at most the smallest upper bound `bⱼ/aⱼ` over `aⱼ < 0`.

In this machine model every instruction addresses fixed tape cells and the
only data movement is a whole-tape shift, so `aᵢ` (cell `2+i`) and `bᵢ`
(cell `2+m+i`) must be brought together by walking the head `m` cells and
carrying registers along; one round trip per constraint costs `Θ(m)`, hence
the quadratic budget. (The linear budget `C·(m+1)` of the milestone
`bss_decides_one_variable_lp` appears to be unattainable for this reason.)
-/

open Matrix LinearOptimization

/-- **Model sanity, quadratic form.** There is a uniform BSS program deciding,
for every `m` and every one-variable system `aᵢx ≥ bᵢ`, its feasibility
within `C·(m+1)²` steps on the standard input encoding. -/

theorem SmaleNinth.bss_decides_one_variable_lp_quadratic :
    ∃ (P : BSSProgram) (C : ℕ),
      ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          BSSDecidesInTime P (encodeLP A b) (C * (m + 1) ^ 2) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) := by sorry
