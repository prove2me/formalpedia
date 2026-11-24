-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_Supplement_lemma_8
-- name    : ResidualsDRO.Wass.Supplement.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:37:04.716822+00:00
-- url     : https://prove2.me/theorems/50ba77b6-fef9-4cc2-8455-c1bf70f09801
-- title:
--   Lemma 8 (corrected: source/boundary conventions) — eventual cost bounds
-- statement:
--   Let x satisfy the standing ER-DRO hypotheses, and let zhat_n be any optimal selection for the Wasserstein problem with the summable risks and vanishing radii of Assumption 6. Write vhat_n for its optimal value, g for true cost, and z* for any true minimizer. Under Assumptions 1 and 2 and i.i.d. errors, eventually almost surely
--
--   $$v^*(x)\le g(\widehat z_n;x)\le\widehat v_n(x).$$
--
--   If Assumption 4 holds with cost Lipschitz constant L₁(z), then eventually almost surely
--
--   $$\widehat v_n(x)\le v^*(x)+2L_1(z^*)\zeta_n.$$
--
--   If Assumption 5 holds, including p≥2, with gradient Lipschitz constant L₂(z), then eventually almost surely
--
--   $$\widehat v_n(x)\le v^*(x)+2\big(E\|\nabla c(z^*,Y)\|^2\big)^{1/2}\zeta_n+4L_2(z^*)\zeta_n^2.$$
--
--   All three clauses belong to this item. They provide the sandwich and quantitative bounds for Theorems 9–11.
--
--   Differences from the source:
--
--   - encoding: positive sample sizes and almost-everywhere covariates in the Euclidean ER-DRO model → Fin n with n≥1 and a fixed covariate satisfying Standing; extended nonnegative errors, probability tails and full Lq including q=∞; reason: these are the source objects and conventions; minima and optimizer sets are constructed and real conversions require finite objectives
--   - generalization: measurable regression estimates and optimal selections → outer probabilities permit arbitrary selections satisfying the same optimality equalities; reason: all probability bounds follow from pathwise containment in the displayed measurable bounding events; measurable source selections are included
--   - correction: radius (10) prints log(c₁/α) in κ^(2) → reuse the published radius with log(2c₁/α); reason: p. 15 states that Lemma 2 is inverted at α/2; this is the published base correction and is not re-audited here
--   - generalization: the observations follow the joint covariate/error model and the regression estimate is constructed from the first n observations → the reduced interface retains support, the conditional response law and the displayed statistical assumptions, without requiring a joint training-covariate law, covariate/error independence or dependence of the estimator only on the first n observations; reason: the estimates below use only the explicit statistical predicates and pathwise residual/projection identities; every source data model supplies this interface, so no source instance is excluded
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Mathematical Programming (2023), accepted manuscript, https://doi.org/10.1007/s10107-023-02014-7, p. 16, Lemma 8

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Supplement_Infinity

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Wass.Supplement

/-- Full source conclusion, at a fixed covariate satisfying the almost-everywhere hypotheses; sample sizes start at one. -/
theorem lemma_8
    {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model dx dy dz Ω) (P : Measure Ω) (x : E dx)
    (p a c₁ c₂ : ℝ) (κ : ℕ → ℝ → ℝ) (α : ℕ → ℝ)
    (h : WAssumptions M P x p a c₁ c₂ κ α)
    (zhat : ℕ → Ω → E dz)
    (hz : WSelect M x p (radii κ p a c₁ c₂ dy α) zhat)
    (zstar : E dz) (hstar : zstar ∈ solutions M x)
    (L₁ L₂ : E dz → ℝ) (G : E dz → E dy → E dy) :
    (∀ᵐ ω ∂P, ∀ᶠ n in atTop, vstar M x ≤ g M x (zhat n ω) ∧
      g M x (zhat n ω) ≤ wvalue M x p (radii κ p a c₁ c₂ dy α n) n ω) ∧
    (A4 M L₁ → ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      wvalue M x p (radii κ p a c₁ c₂ dy α n) n ω ≤ vstar M x + 2 * L₁ zstar * (radii κ p a c₁ c₂ dy α n)) ∧
    (A5 M x p L₂ G → ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      wvalue M x p (radii κ p a c₁ c₂ dy α n) n ω ≤ vstar M x + 2 * gradMoment M G x zstar * (radii κ p a c₁ c₂ dy α n) +
        4 * L₂ zstar * (radii κ p a c₁ c₂ dy α n) ^ 2) := by sorry

end ResidualsDRO.Wass.Supplement
