-- Prove2me | Theorems.Thm_SherbrookeMetric_PointEstimate_point_estimate_understates_backorders
-- name    : SherbrookeMetric.PointEstimate.point_estimate_understates_backorders
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:30.648283+00:00
-- url     : https://prove2.me/theorems/83dc1c94-795d-4b8d-8350-da8a4f48591a
-- title:
--   pp. 138–139 — under Poisson demand and positive spare stock, a point estimate of mean demand understates expected backorders
-- statement:
--   Let $B(s \mid \lambda) = \sum_{x=s+1}^{\infty}(x - s)\,e^{-\lambda}\lambda^x/x!$ be the expected backorders at spare stock $s$ under Poisson demand with mean $\lambda$.
--
--   Suppose the true mean demand is unknown and takes the positive values $\lambda_k$, $k \in K$ ($K$ finite), with probabilities $w_k \ge 0$, $\sum_k w_k = 1$. The **point estimate** of mean demand is the mean of this distribution,
--   $$\bar\lambda = \sum_k w_k \lambda_k,$$
--   and the expected backorders under the uncertainty are $\sum_k w_k\,B(s \mid \lambda_k)$. Then:
--
--   1. if mean demand can assume more than one value — there are $k, k'$ with $w_k > 0$, $w_{k'} > 0$ and $\lambda_k \ne \lambda_{k'}$ — then for every spare stock $s \ge 1$,
--   $$B(s \mid \bar\lambda) < \sum_k w_k\, B(s \mid \lambda_k);$$
--   2. for spare stock $s = 0$, always
--   $$B(0 \mid \bar\lambda) = \sum_k w_k\, B(0 \mid \lambda_k).$$
--
--   This is the assertion of Sherbrooke (1968), pp. 138–139: "For the case of Poisson demand and positive spare stock, … backorders computed from a point estimate of mean demand always understate the correct value when mean demand can assume more than one value", and "For a spare stock of zero … backorders computed from a point estimate are identical to backorders computed from a range of estimates." It is the paper's argument that a Bayesian treatment of demand uncertainty is needed for every item, not only for low-demand items.
--
--   **Formalization Note** The paper's uncertainty about the mean is a gamma prior that its procedure discretizes to "from five to ten possible values"; the statement uses an arbitrary finite prior with positive support points, which covers the paper's discretization and its two-point example. "Can assume more than one value" is read as two distinct support points of positive probability; without it the strict inequality fails. The point estimate is the prior mean, as the paper assumes ("the initial estimate is the mean of the true mean demand distribution", p. 139).
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), pp. 138–139, Demand Prediction

import Mathlib
import Definitions.Def_SherbrookeMetric_PointEstimate_backorders

namespace SherbrookeMetric.PointEstimate

/-- Sherbrooke (1968), pp. 138–139: let true mean demand take the positive values `lam k`
with probabilities `w k` (a finite prior) and let the point estimate be the prior mean
`Σ_k w k * lam k`. If mean demand can assume more than one value (two distinct values both
carry positive weight), then for every spare stock `s ≥ 1` the backorders computed from the
point estimate are strictly smaller than the expected backorders under the prior. For spare
stock `0` the two coincide. -/
theorem point_estimate_understates_backorders {K : Type*} [Fintype K] (w lam : K → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) (hlam : ∀ k, 0 < lam k) :
    ((∃ k k', 0 < w k ∧ 0 < w k' ∧ lam k ≠ lam k') →
      ∀ s : ℕ, 1 ≤ s →
        backorders s (∑ k, w k * lam k) < ∑ k, w k * backorders s (lam k)) ∧
    backorders 0 (∑ k, w k * lam k) = ∑ k, w k * backorders 0 (lam k) := by sorry

end SherbrookeMetric.PointEstimate
