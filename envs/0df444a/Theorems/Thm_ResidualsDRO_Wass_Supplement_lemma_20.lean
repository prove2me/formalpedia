-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_Supplement_lemma_20
-- name    : ResidualsDRO.Wass.Supplement.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:45:03.810517+00:00
-- url     : https://prove2.me/theorems/6973731c-2b29-4900-8dac-a286a021c021
-- title:
--   Lemma 20 — d_{W,∞}(P̂^ER_n(x), P_{Y|X=x}) ≤ 2 sup_x ‖f*(x) − f̂_n(x)‖ + d_{W,∞}(P*_n(x), P_{Y|X=x})
-- statement:
--   For each admissible covariate x and positive sample size n, let Phat_n be the projected residual empirical law, P*_n the empirical law of f*(x)+ε_i, and P_{Y|X=x} its population law. For any realization of the training sample with covariates in 𝒳 and true scenarios in 𝒴,
--
--   $$d_{W,\infty}(\widehat P^{ER}_n(x),P_{Y\mid X=x})\le2\sup_{u\in\mathcal X}\|f^*(u)-\widehat f_n(u)\|+d_{W,\infty}(P^*_n(x),P_{Y\mid X=x}).$$
--
--   The projection is the nearest-point map onto the nonempty closed convex response range. All suprema and transport distances are extended nonnegative values, so an unbounded estimation error stays infinite. This is a deterministic comparison and does not assume regression consistency or independent observations.
--
--   Differences from the source:
--
--   - encoding: positive sample sizes and almost-everywhere covariates in the Euclidean ER-DRO model → Fin n with n≥1 and a fixed covariate satisfying Standing; extended nonnegative errors, probability tails and full Lq including q=∞; reason: these are the source objects and conventions; minima and optimizer sets are constructed and real conversions require finite objectives
--   - generalization: the comparison law is the source conditional probability distribution → no probability, zero-mean or independence restriction on the comparison measure is needed in this deterministic bound; reason: triangle inequality and the paired empirical coupling give the same inequality for any comparison measure; unequal total masses make the right-hand transport distance infinite
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Mathematical Programming (2023), accepted manuscript, https://doi.org/10.1007/s10107-023-02014-7, p. 26, Lemma 20

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Supplement_Infinity

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Wass.Supplement

/-- Full source conclusion, at a fixed covariate satisfying the almost-everywhere hypotheses; sample sizes start at one. -/
theorem lemma_20
    {dx dy dz n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model dx dy dz Ω) (x : E dx) (ω : Ω) (hn : 1 ≤ n)
    (hx : x ∈ M.X) (hxs : ∀ i : Fin n, M.D.xs i ω ∈ M.X)
    (hY : M.D.𝒴.Nonempty) (hclosed : IsClosed M.D.𝒴) (hconvex : Convex ℝ M.D.𝒴)
    (hproj : IsNearestPointProj M.D.𝒴 M.D.proj)
    (hs : ∀ i : Fin n, M.D.fstar x + M.D.eps i ω ∈ M.D.𝒴) :
    winfty (PER M x n ω) (law M x) ≤
      2 * predictionSup M n ω + winfty (Pstar M x n ω) (law M x) := by sorry

end ResidualsDRO.Wass.Supplement
