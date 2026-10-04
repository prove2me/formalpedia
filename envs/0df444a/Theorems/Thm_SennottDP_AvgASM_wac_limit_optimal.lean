-- Prove2me | Theorems.Thm_SennottDP_AvgASM_wac_limit_optimal
-- name    : SennottDP.AvgASM.wac_limit_optimal
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-01T10:00:21.249103+00:00
-- url     : https://prove2.me/theorems/0ff4ab01-6c48-425e-8253-79b7278ac96a
-- title:
--   Proposition 8.7.1 — under (WAC) the conclusions of Theorem 8.1.1 hold
-- statement:
--   Let $(\Delta_N)_{N\ge N_0}$ be an approximating sequence for the MDC $\Delta$, and let the constants $J^N$ and functions $r^N$ satisfy the (WAC) assumptions. Then the conclusions of Theorem 8.1.1 are valid:
--   1. the limit $J^*=\lim_{N\to\infty}J^N$ exists and is the minimum average cost in $\Delta$, i.e.
--   $$J(i)=J^*\qquad\text{for all } i\in S;$$
--   2. any limit point $e^*$ of a sequence $e^N$ of stationary policies realizing the minimum in (8.1) is average cost optimal for $\Delta$.
--
--   Since (AC) implies (WAC) (take $Q(\cdot)\equiv Q$), this is a strengthening of Theorem 8.1.1 that allows the lower bound on the relative values to depend on the state.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 194, Proposition 8.7.1

import Mathlib
import Definitions.Def_SennottDP_AvgASM_Assumptions

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.AvgASM

/-- **Proposition 8.7.1** (Sennott 1999, p. 194). Assume that the (WAC) assumptions hold for the
constants `J^N` and functions `r^N` of (WAC1). Then the conclusions of Theorem 8.1.1 are valid:
`lim_{N→∞} J^N` exists and equals the (constant) minimum average cost `J(i)` of `Δ`, and any
limit point of a sequence of stationary policies realizing the minimum in (8.1) is average cost
optimal for `Δ`. -/
theorem wac_limit_optimal {S : Type*} {Act : Type*} [Countable S] {M : MDC S Act}
    (AS : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hWAC : AS.WAC JN rN) :
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, ((avgValue M i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
    ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e N i)) →
      ∀ f : StationaryPolicy M, AS.IsLimitPoint e f → IsAverageOptimal f.toPolicy := by sorry

end SennottDP.AvgASM
