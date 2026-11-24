-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_Supplement_theorem_11
-- name    : ResidualsDRO.Wass.Supplement.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:39:54.564806+00:00
-- url     : https://prove2.me/theorems/368fb2e9-c7d5-4251-aba6-e9ce2af9a623
-- title:
--   Theorem 11 (corrected: source/boundary conventions) — mean rates
-- statement:
--   Let 1≤q≤∞, let X have law P_X independently of the training sample, and let z*(x) be a true optimal selection. Under Assumptions 1, 3, 6 and 7 and i.i.d. errors, use the uniform estimation bound κ_n(α) in (10), so its radius ζ_n(α_n) is independent of x. Suppose either Assumption 4 holds and L₁(z*(X)) has finite Lq norm, or Assumption 5 holds and both its gradient second-moment square root and L₂(z*(X)) have finite Lq norms. Then
--
--   $$\|\widehat v_n(X)-v^*(X)\|_{L^q}=O_p(\zeta_n(\alpha_n)),\qquad\|g(\widehat z_n(X);X)-v^*(X)\|_{L^q}=O_p(\zeta_n(\alpha_n)).$$
--
--   The Lq norm is over a fresh covariate with data held fixed; q=∞ means the essential supremum. Assumption 2 is not added: the estimation hypothesis is Assumption 7. This is convergence averaged over the covariates.
--
--   Differences from the source:
--
--   - encoding: positive sample sizes and almost-everywhere covariates in the Euclidean ER-DRO model → Fin n with n≥1 and a fixed covariate satisfying Standing; extended nonnegative errors, probability tails and full Lq including q=∞; reason: these are the source objects and conventions; minima and optimizer sets are constructed and real conversions require finite objectives
--   - generalization: measurable regression estimates and optimal selections → outer probabilities permit arbitrary selections satisfying the same optimality equalities; reason: all probability bounds follow from pathwise containment in the displayed measurable bounding events; measurable source selections are included
--   - correction: radius (10) prints log(c₁/α) in κ^(2) → reuse the published radius with log(2c₁/α); reason: p. 15 states that Lemma 2 is inverted at α/2; this is the published base correction and is not re-audited here
--   - generalization: the observations follow the joint covariate/error model and the regression estimate is constructed from the first n observations → the reduced interface retains support, the conditional response law and the displayed statistical assumptions, without requiring a joint training-covariate law, covariate/error independence or dependence of the estimator only on the first n observations; reason: the estimates below use only the explicit statistical predicates and pathwise residual/projection identities; every source data model supplies this interface, so no source instance is excluded
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Mathematical Programming (2023), accepted manuscript, https://doi.org/10.1007/s10107-023-02014-7, p. 18, Theorem 11

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Supplement_Infinity

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Wass.Supplement

/-- Full source conclusion, at a fixed covariate satisfying the almost-everywhere hypotheses; sample sizes start at one. -/
theorem theorem_11
    {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model dx dy dz Ω) (P : Measure Ω)
    (p a c₁ c₂ : ℝ) (κ : ℕ → ℝ → ℝ) (α : ℕ → ℝ)
    (q : ℝ≥0∞) (hq : 1 ≤ q)
    (h : ∀ᵐ x ∂M.PX, Standing M P x ∧ Concentration M P x p a c₁ c₂ ∧
      ∀ n, 1 ≤ n → WRegular M x p (radii κ p a c₁ c₂ dy α n) n)
    (hiid : IID M P) (h3 : A3 M p) (h7 : A7 M P κ)
    (h6 : A6 α (radii κ p a c₁ c₂ dy α))
    (zstar : E dx → E dz) (hs : ∀ᵐ x ∂M.PX, zstar x ∈ solutions M x)
    (L₁ L₂ : E dz → ℝ) (G : E dz → E dy → E dy)
    (h45 : (A4 M L₁ ∧ lq M q (fun x => L₁ (zstar x)) < ⊤) ∨
      ((∀ᵐ x ∂M.PX, A5 M x p L₂ G) ∧
        lq M q (fun x => gradMoment M G x (zstar x)) < ⊤ ∧
        lq M q (fun x => L₂ (zstar x)) < ⊤))
    (zhat : ℕ → Ω → E dx → E dz)
    (hz : ∀ᵐ x ∂M.PX, WSelect M x p (radii κ p a c₁ c₂ dy α)
      (fun n ω => zhat n ω x)) :
    Unified.IsBigOp P (fun n ω => lq M q (fun x =>
      wvalue M x p (radii κ p a c₁ c₂ dy α n) n ω - vstar M x))
      (radii κ p a c₁ c₂ dy α) ∧
    Unified.IsBigOp P (fun n ω => lq M q (fun x => g M x (zhat n ω x) - vstar M x))
      (radii κ p a c₁ c₂ dy α) := by sorry

end ResidualsDRO.Wass.Supplement
