-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_Supplement_theorem_9
-- name    : ResidualsDRO.Wass.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:37:42.088858+00:00
-- url     : https://prove2.me/theorems/b46be9c7-4b98-4055-8028-a03b0ee3303f
-- title:
--   Theorem 9 (corrected: source/boundary conventions) — consistency
-- statement:
--   Fix a covariate x where the source assumptions hold. Under Assumptions 1, 2, 3 and 6 and i.i.d. errors, let vhat_n and zhat_n be the optimal value and any optimal selection of the ER-DRO problem with the radius of (10). Then
--
--   $$\widehat v_n(x)\xrightarrow{p}v^*(x),\qquad\operatorname{dist}(\widehat z_n(x),S^*(x))\xrightarrow{p}0,\qquad g(\widehat z_n(x);x)\xrightarrow{p}v^*(x).$$
--
--   Here g is the true conditional expectation and S* is its entire minimizer set on the nonempty compact decision set. All three consistency and asymptotic optimality conclusions are stated together.
--
--   Differences from the source:
--
--   - encoding: positive sample sizes and almost-everywhere covariates in the Euclidean ER-DRO model → Fin n with n≥1 and a fixed covariate satisfying Standing; extended nonnegative errors, probability tails and full Lq including q=∞; reason: these are the source objects and conventions; minima and optimizer sets are constructed and real conversions require finite objectives
--   - generalization: measurable regression estimates and optimal selections → outer probabilities permit arbitrary selections satisfying the same optimality equalities; reason: all probability bounds follow from pathwise containment in the displayed measurable bounding events; measurable source selections are included
--   - correction: radius (10) prints log(c₁/α) in κ^(2) → reuse the published radius with log(2c₁/α); reason: p. 15 states that Lemma 2 is inverted at α/2; this is the published base correction and is not re-audited here
--   - generalization: the observations follow the joint covariate/error model and the regression estimate is constructed from the first n observations → the reduced interface retains support, the conditional response law and the displayed statistical assumptions, without requiring a joint training-covariate law, covariate/error independence or dependence of the estimator only on the first n observations; reason: the estimates below use only the explicit statistical predicates and pathwise residual/projection identities; every source data model supplies this interface, so no source instance is excluded
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Mathematical Programming (2023), accepted manuscript, https://doi.org/10.1007/s10107-023-02014-7, p. 16, Theorem 9

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Supplement_Infinity

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Wass.Supplement

/-- Full source conclusion, at a fixed covariate satisfying the almost-everywhere hypotheses; sample sizes start at one. -/
theorem theorem_9
    {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model dx dy dz Ω) (P : Measure Ω) (x : E dx)
    (p a c₁ c₂ : ℝ) (κ : ℕ → ℝ → ℝ) (α : ℕ → ℝ)
    (h : WAssumptions M P x p a c₁ c₂ κ α)
    (h3 : A3 M p)
    (zhat : ℕ → Ω → E dz)
    (hz : WSelect M x p (radii κ p a c₁ c₂ dy α) zhat)
    : Vanishes P (fun n ω => error (wvalue M x p (radii κ p a c₁ c₂ dy α n) n ω) (vstar M x)) ∧
    Vanishes P (fun n ω => ⨅ z ∈ solutions M x, edist (zhat n ω) z) ∧
    Vanishes P (fun n ω => error (g M x (zhat n ω)) (vstar M x)) := by sorry

end ResidualsDRO.Wass.Supplement
