-- Prove2me | Theorems.Thm_SecondBestTrade_HalfEfficiency_one_factor_per_side
-- name    : SecondBestTrade.HalfEfficiency.one_factor_per_side
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:56.425576+00:00
-- url     : https://prove2.me/theorems/501c027a-45f4-4da4-be90-d5fbbf742f68
-- title:
--   Lemma 7.1 — One factor per side
-- statement:
--   Fix a useful dual and nonnegative shared clock values $\theta_B,\theta_S$. Start agents independently from the product prior and run their chains with independent randomness conditional on these clocks. Each buyer's terminal law is $f_i e^{\theta_B Q_i}$ and each seller's is $g_j e^{\theta_S Q_j}$. Then
--   $$\mathbb E[\widetilde H(\widehat v,\widehat c)\mid\theta_B,\theta_S]\le e^{\kappa(\theta_B+\theta_S)}\mathbb E_\pi[\widetilde H(v,c)].$$
--   The bound holds for every market in the full downward-closed model and incurs one density factor per side, independently of the number of buyers and sellers.
--
--   Differences from the source:
--   - encoding: finite agent, trade and support sets with product-prior expectations → Fin labels, an injective nonnegative-vector support embedding, and finite product-weighted sums; reason: bijections cover every finite source market, and summing an overwritten own coordinate multiplies by its total probability one
--   - encoding: conditional expected virtual surplus under shared clocks → the finite sum under the fixed-clock product of terminal laws, for every nonnegative clock pair; reason: conditioning leaves independent agent transitions and independent initial priors; the finite product sum is exactly that conditional law
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Lemma 7.1 — One factor per side, printed p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Dual

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Lemma 7.1, printed p. 13 (PDF p. 14). Conditional expectation is the fixed-clock finite product sum. -/
theorem one_factor_per_side (N : Market) (z : Dual N) (hz : useful N z)
    (thetaB thetaS : ℝ) (hB : 0 ≤ thetaB) (hS : 0 ≤ thetaS) :
    conditionalSurplus N z thetaB thetaS ≤
      Real.exp (kappa (z.tau : ℝ) * (thetaB + thetaS)) * expect N (Hvirtual N z) := by sorry

end SecondBestTrade.HalfEfficiency
