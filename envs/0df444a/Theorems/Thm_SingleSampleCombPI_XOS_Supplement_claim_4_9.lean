-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_claim_4_9
-- name    : SingleSampleCombPI.XOS.Supplement.claim_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:43:36.144196+00:00
-- url     : https://prove2.me/theorems/07c86209-fd02-4f59-9f1b-90e83fd65f7c
-- title:
--   Claim 4.9 — Continuous surrogate attains a maximum, and every maximizer is a free-disposal greedy choice
-- statement:
--   Fix any finite previous history $H$ of cube allocations with nonnegative prices frozen at those allocations. Let the arriving buyer have a normalized monotone continuous valuation $v$ and a valid one-sided supporting map. Define
--   $$\Phi(x)=v(x)+\mathrm{FD}_{1-x}(H),\qquad x\in[0,1]^m.$$
--   The function $\Phi$ attains its maximum. Every maximizer $x$ also maximizes
--   $$\mathrm{FD}(H\mathbin{\|}(x,q_v(x)))-\mathrm{FD}(H)$$
--   over the whole cube. The supporting map need not be continuous. This is the surrogate-to-greedy correspondence needed for the continuous buyer-wise allocation rule.
--
--   Differences from the source:
--   - generalization: the previous provisional allocations of Algorithm 5 → any finite history of cube allocations with nonnegative frozen prices; reason: every source history is included; each arbitrary frozen price vector is itself the valid supporting price of its linear valuation, and the claim uses only these frozen records
--   - encoding: the truncated free-disposal integral over [0,∞) → real Lebesgue integral over (0,∞); reason: on the capacities used in this statement the integrands are bounded finite step functions with bounded support; changing the endpoint does not change the value and no nonintegrable default is used
--   - encoding: valuations and one-sided supporting-price maps on the source allocation domains → published Buyer, Regime and cube interfaces with real-valued functions evaluated only on the allocation domain; reason: the stored demand field is unused in noncomputational continuous statements; no support, continuity or concavity condition is added to the source valuation class
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Claim 4.9, printed p. 22 / PDF p. 24; proof printed 23 / PDF 25.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Continuous

namespace SingleSampleCombPI.XOS.Supplement

/-- Claim 4.9, printed p. 22 / PDF p. 24; proof PDF p. 25. Continuity is
required for the arriving valuation, not its supporting-price map. Every
surrogate maximizer maximizes the actual frozen-price FD increment. -/
theorem claim_4_9 {m : ℕ} (H : FrozenHistory m) (hH : H.Valid)
    (b : Buyer m) (hb : b.Valid .divisible)
    (hc : ContinuousOn b.v {x | InDom .divisible x}) :
    (∃ x : Vec m, CubeMaximizer (surrogate H b) x) ∧
    ∀ x : Cube m, CubeMaximizer (surrogate H b) x.1 →
      ∀ y : Cube m,
        historyFD (H ++ [freeze b y]) - historyFD H ≤
          historyFD (H ++ [freeze b x]) - historyFD H := by sorry

end SingleSampleCombPI.XOS.Supplement
