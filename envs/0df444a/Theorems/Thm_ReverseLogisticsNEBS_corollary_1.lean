-- Prove2me | Theorems.Thm_ReverseLogisticsNEBS_corollary_1
-- name    : ReverseLogisticsNEBS.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:57.768164+00:00
-- url     : https://prove2.me/theorems/e82e6310-1523-4187-9da3-402032a9b810
-- title:
--   Corollary 1 — optimal relaxed echelon schedules are unidirectional (corrected: at locations with $c^E_j, c^R_j > 0$)
-- statement:
--   In every period $t$, at every Markov state $\omega$ and nested echelon state $y_t$, and for every continuation function $F$, if $(Y^E_t, Y^R_t, Y_t)$ is an optimal decision of the relaxed problem (10), then at every location $j$ with $c^E_j > 0$ and $c^R_j > 0$:
--   $$
--   \big(Y^E_{jt} = y_{jt}\ \text{and}\ Y_{jt} = Y^R_{jt}\big)\quad\text{or}\quad Y^R_{jt} = Y^E_{jt}.
--   $$
--
--   This is Theorem 1 in echelon variables: no expedited or regular order at $j$, or no reverse order at $j$. It is what makes the relaxation exact (Theorem 2).
--
--   **Formalization Note** Optimality is among relaxed-feasible schedules with an integrable continuation.
--
--   Differences from the source:
--   - correction: at each location j → at each location j with c^E_j > 0 and c^R_j > 0; reason: same counterexample as Theorem 1 (N = 1, c^R_1 = −3.9: the unique optimal echelon schedule at y = 20 is Y^E = 20, Y^R = 0, Y = 10, which satisfies neither alternative)
--   - reading: If (Y^E_t, Y^R_t, Y_t) are optimal echelon schedules … then → every optimal schedule; reason: as in Theorem 1 (paper.md item 8)
--   - generalization: the continuation f̃_{t+1} → an arbitrary continuation function F; reason: the improving moves keep Y_t, hence the continuation term; f̃_{t+1} is a special case
--   - encoding: optimal = attains the min of the objective → optimal among the feasible decisions whose expected continuation is finite (integrable); reason: a decision with an infinite expected continuation has infinite cost in the paper; Lean's Bochner integral would give it the junk value 0
--   - reading: unit holding and backlogging costs H_j, p of unstated sign (pp.9–10) → H_j ≥ 0 and p ≥ 0 (Model.Standing); reason: unit costs; the field's standing convention, also what makes γ_t nonincreasing
--   - reading: stochastic customer demand D_t (p.7), E_ω[D_t(ω)] in γ_t (p.11) → every demand law supported on [0, ∞) with a finite mean (Model.Standing); reason: demand is a nonnegative quantity and γ_t needs E[D] < ∞ (paper.md item 3)
--   - encoding: h_j := H_j − H_{j+1} for j ∈ [1, N] with H_{N+1} undefined (p.11) → H_{N+1} := 0; reason: the only value under which (4) and (5) agree; changes no instance
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), Corollary 1, p.13

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_Sched

open MeasureTheory ProbabilityTheory

namespace ReverseLogisticsNEBS

/-- **Corollary 1** (Angelus–Özer, SSRN 3508009, Dec. 21, 2019, p.13), corrected: if
`(Y^E_t, Y^R_t, Y_t)` are optimal echelon schedules for the relaxed problem (10) in period `t` (for
any continuation function `F`), then at every location `j` with `c^E_j > 0` and `c^R_j > 0`,
either `Y^E_jt = y_jt` and `Y_jt = Y^R_jt`, or `Y^R_jt = Y^E_jt`; for every nested `y_t` and every
`ω`.

**Formalization Note.** The printed corollary claims this at every location; like Theorem 1 it
fails when `c^R_j < 0`, or by ties when `c^R_j = 0` or `c^E_N = 0`. The continuation `F` is
arbitrary (it is `f̃_{t+1}` in the paper). -/
theorem corollary_1 {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (M : Model N Ω) (hM : M.Standing) (t : ℕ)
    (F : Ω → (Fin N → ℝ) → ℝ) (ω : Ω) (y : Fin N → ℝ) (hy : Monotone y) (s : Sched N)
    (hs : M.IsOptimalDecision t F (Sched.FeasRelax y) ω s) :
    ∀ j, 0 < M.cE j → 0 < M.cR j → Sched.UnidirAt y s j := by sorry

end ReverseLogisticsNEBS
