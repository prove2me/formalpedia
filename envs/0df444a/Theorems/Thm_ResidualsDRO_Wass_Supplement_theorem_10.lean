-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_Supplement_theorem_10
-- name    : ResidualsDRO.Wass.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:38:48.626127+00:00
-- url     : https://prove2.me/theorems/8ffb283a-7723-4d91-8e67-653114707383
-- title:
--   Theorem 10 (corrected: source/boundary conventions) — pointwise rates
-- statement:
--   Under all hypotheses of Theorem 9, assume either the Lipschitz cost condition of Assumption 4 or the smooth cost condition of Assumption 5. At every covariate x satisfying those hypotheses, for every optimal ER-DRO selection,
--
--   $$|\widehat v_n(x)-v^*(x)|=O_p(\zeta_n(\alpha_n,x)),\qquad |g(\widehat z_n(x);x)-v^*(x)|=O_p(\zeta_n(\alpha_n,x)).$$
--
--   The alternative assumptions are a disjunction, with p≥2 included in the smooth branch. The rate is the actual radius (10), not a free sequence chosen after the solution. The constant in O_p is uniform in n.
--
--   Differences from the source:
--
--   - encoding: positive sample sizes and almost-everywhere covariates in the Euclidean ER-DRO model → Fin n with n≥1 and a fixed covariate satisfying Standing; extended nonnegative errors, probability tails and full Lq including q=∞; reason: these are the source objects and conventions; minima and optimizer sets are constructed and real conversions require finite objectives
--   - generalization: measurable regression estimates and optimal selections → outer probabilities permit arbitrary selections satisfying the same optimality equalities; reason: all probability bounds follow from pathwise containment in the displayed measurable bounding events; measurable source selections are included
--   - correction: radius (10) prints log(c₁/α) in κ^(2) → reuse the published radius with log(2c₁/α); reason: p. 15 states that Lemma 2 is inverted at α/2; this is the published base correction and is not re-audited here
--   - generalization: the observations follow the joint covariate/error model and the regression estimate is constructed from the first n observations → the reduced interface retains support, the conditional response law and the displayed statistical assumptions, without requiring a joint training-covariate law, covariate/error independence or dependence of the estimator only on the first n observations; reason: the estimates below use only the explicit statistical predicates and pathwise residual/projection identities; every source data model supplies this interface, so no source instance is excluded
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Mathematical Programming (2023), accepted manuscript, https://doi.org/10.1007/s10107-023-02014-7, p. 16, Theorem 10

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Supplement_Infinity

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Wass.Supplement

/-- Full source conclusion, at a fixed covariate satisfying the almost-everywhere hypotheses; sample sizes start at one. -/
theorem theorem_10
    {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model dx dy dz Ω) (P : Measure Ω) (x : E dx)
    (p a c₁ c₂ : ℝ) (κ : ℕ → ℝ → ℝ) (α : ℕ → ℝ)
    (h : WAssumptions M P x p a c₁ c₂ κ α)
    (h3 : A3 M p) (L₁ L₂ : E dz → ℝ) (G : E dz → E dy → E dy)
    (h45 : A4 M L₁ ∨ A5 M x p L₂ G)
    (zhat : ℕ → Ω → E dz)
    (hz : WSelect M x p (radii κ p a c₁ c₂ dy α) zhat)
    : Unified.IsBigOp P (fun n ω => error (wvalue M x p (radii κ p a c₁ c₂ dy α n) n ω) (vstar M x))
      (radii κ p a c₁ c₂ dy α) ∧
    Unified.IsBigOp P (fun n ω => error (g M x (zhat n ω)) (vstar M x))
      (radii κ p a c₁ c₂ dy α) := by sorry

end ResidualsDRO.Wass.Supplement
