-- Prove2me | Theorems.Thm_SecondBestTrade_HalfEfficiency_prior_density
-- name    : SecondBestTrade.HalfEfficiency.prior_density
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:03.48294+00:00
-- url     : https://prove2.me/theorems/67d0c446-9a6d-45c4-bb1c-e4790a407da9
-- title:
--   Lemma 5.5 — Prior-density bounds
-- statement:
--   At every useful dual and every $\theta\ge0$, the terminal distribution of each agent $a$ started from its prior $f_a$ obeys the componentwise bound
--   $$f_a e^{\theta Q_a}\le e^{\kappa\theta}f_a,\qquad \kappa=\frac{\tau}{1+\tau}.$$
--   Averaging over the independent rate-one exponential clock also gives
--   $$f_a(I-Q_a)^{-1}\le(1+\tau)f_a.$$
--   Both assertions apply to every buyer and every seller and every support coordinate. The factor is uniform over times, types and the number of agents.
--
--   Differences from the source:
--   - encoding: finite agent, trade and support sets with product-prior expectations → Fin labels, an injective nonnegative-vector support embedding, and finite product-weighted sums; reason: bijections cover every finite source market, and summing an overwritten own coordinate multiplies by its total probability one
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Lemma 5.5 — Prior-density bounds, printed p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Dual

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Lemma 5.5, printed p. 11 (PDF p. 12), including the integrated inequalities. -/
theorem prior_density (N : Market) (z : Dual N) (hz : useful N z) :
    (∀ theta : ℝ, 0 ≤ theta → ∀ a t,
      terminalMass N z a theta t ≤ Real.exp (kappa (z.tau : ℝ) * theta) * N.mass a t) ∧
    (∀ a t, (∑ s, N.mass a s * resolvent N z a s t) ≤
      (1 + (z.tau : ℝ)) * N.mass a t) := by sorry

end SecondBestTrade.HalfEfficiency
