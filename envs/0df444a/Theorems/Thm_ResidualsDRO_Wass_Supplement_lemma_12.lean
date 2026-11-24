-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_Supplement_lemma_12
-- name    : ResidualsDRO.Wass.Supplement.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:41:03.297345+00:00
-- url     : https://prove2.me/theorems/a651dbf8-f9da-4c97-8675-80796e197f28
-- title:
--   Lemma 12 (corrected: source/boundary conventions) — cost tails
-- statement:
--   Under Assumptions 1, 2, 3 and 8, i.i.d. errors, and either Assumption 4 or Assumption 5, fix an admissible covariate x and any tolerance t>0. There exist Γ>0, γ>0 and an admissible estimation bound κ_{p,n}, chosen as in Appendix A.5, for which the radius (10) at risk α_n=Γ exp(−nγ) satisfies, for every optimal selection and every positive n with α_n<1,
--
--   $$\mathbb P\{g(\widehat z_n(x);x)>v^*(x)+t\}\le2\Gamma e^{-n\gamma}.$$
--
--   The radius and admissible bound are chosen before the optimal selection. Its real-valued lower semicontinuous objective is the standing condition on (8). The risk-domain restriction adds no substantive exception: if α_n≥1, the displayed probability bound is automatic. This cost-tail estimate supports Theorem 13.
--
--   Differences from the source:
--
--   - encoding: positive sample sizes and almost-everywhere covariates in the Euclidean ER-DRO model → Fin n with n≥1 and a fixed covariate satisfying Standing; extended nonnegative errors, probability tails and full Lq including q=∞; reason: these are the source objects and conventions; minima and optimizer sets are constructed and real conversions require finite objectives
--   - generalization: measurable regression estimates and optimal selections → outer probabilities permit arbitrary selections satisfying the same optimality equalities; reason: all probability bounds follow from pathwise containment in the displayed measurable bounding events; measurable source selections are included
--   - correction: radius (10) prints log(c₁/α) in κ^(2) → reuse the published radius with log(2c₁/α); reason: p. 15 states that Lemma 2 is inverted at α/2; this is the published base correction and is not re-audited here
--   - correction: Lemma 12 and Theorem 13 appear to allow any admissible estimation bound κ → existentially choose an admissible κ together with Γ,γ, then quantify over all optimal solutions at all n with α_n<1; reason: Appendix A.5, p. 44 explicitly chooses κ; exact regression with a fixed oversized κ defeats the arbitrary-bound reading (HARD.md); α_n≥1 yields a trivial upper bound ≥2
--   - generalization: the observations follow the joint covariate/error model and the regression estimate is constructed from the first n observations → the reduced interface retains support, the conditional response law and the displayed statistical assumptions, without requiring a joint training-covariate law, covariate/error independence or dependence of the estimator only on the first n observations; reason: the estimates below use only the explicit statistical predicates and pathwise residual/projection identities; every source data model supplies this interface, so no source instance is excluded
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Mathematical Programming (2023), accepted manuscript, https://doi.org/10.1007/s10107-023-02014-7, p. 19, Lemma 12

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Supplement_Infinity

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Wass.Supplement

/-- Corrected choice of admissible κ: Appendix A.5, p. 44. For arbitrary admissible κ the printed assertion fails. -/
theorem lemma_12
    {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model dx dy dz Ω) (P : Measure Ω) (x : E dx)
    (p a c₁ c₂ : ℝ) (h : Standing M P x) (hiid : IID M P)
    (hc : Concentration M P x p a c₁ c₂) (h3 : A3 M p)
    (κ₀ : ℕ → ℝ → ℝ) (h2 : A2 M P p x κ₀) (h8 : A8 M P x p)
    (L₁ L₂ : E dz → ℝ) (G : E dz → E dy → E dy)
    (h45 : A4 M L₁ ∨ A5 M x p L₂ G)
    (t : ℝ) (ht : 0 < t) :
    ∃ Γ γ : ℝ, 0 < Γ ∧ 0 < γ ∧ ∃ κ : ℕ → ℝ → ℝ, A2 M P p x κ ∧
      ∀ n : ℕ, 1 ≤ n → Γ * Real.exp (-(n : ℝ) * γ) < 1 →
      WRegular M x p (radius (κ n) c₁ c₂ a p dy n
        (Γ * Real.exp (-(n : ℝ) * γ))) n →
      ∀ z : Ω → E dz,
      (∀ ω, z ω ∈ M.Z ∧ wobj M x p (radius (κ n) c₁ c₂ a p dy n
        (Γ * Real.exp (-(n : ℝ) * γ))) n ω (z ω) =
        (wvalue M x p (radius (κ n) c₁ c₂ a p dy n
          (Γ * Real.exp (-(n : ℝ) * γ))) n ω : EReal)) →
      P {ω | g M x (z ω) > vstar M x + t} ≤ ENNReal.ofReal (2 * Γ * Real.exp (-(n : ℝ) * γ)) := by sorry

end ResidualsDRO.Wass.Supplement
