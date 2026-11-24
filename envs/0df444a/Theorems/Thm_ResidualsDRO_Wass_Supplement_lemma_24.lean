-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_Supplement_lemma_24
-- name    : ResidualsDRO.Wass.Supplement.lemma_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:36:02.582397+00:00
-- url     : https://prove2.me/theorems/cad25b5d-2c79-45dc-88ed-c6416a19ae96
-- title:
--   Lemma 24 (corrected: source/boundary conventions) — ball convergence
-- statement:
--   For a fixed admissible covariate x, let Q_n(x) be any sequence of random probability distributions in the ER Wasserstein ball with radius ζ_n(α_n,x) of (10). Under Assumptions 1, 2 and 6 and i.i.d. errors, all three assertions hold:
--
--   $$\mathbb P\{d_{W,p}(P_{Y\mid X=x},Q_n(x))\le2\zeta_n(\alpha_n,x)\}\ge1-\alpha_n,$$
--
--   $$d_{W,p}(P_{Y\mid X=x},Q_n(x))\le2\zeta_n(\alpha_n,x)\text{ eventually almost surely},\qquad d_{W,p}(P_{Y\mid X=x},Q_n(x))\to0\text{ almost surely}.$$
--
--   The sequence is arbitrary, rather than a selected adversarial distribution. The quoted concentration estimate is supplied with constants uniform in n, as in the published base radius. This is the ball-convergence result supporting consistency.
--
--   Differences from the source:
--
--   - encoding: positive sample sizes and almost-everywhere covariates in the Euclidean ER-DRO model → Fin n with n≥1 and a fixed covariate satisfying Standing; extended nonnegative errors, probability tails and full Lq including q=∞; reason: these are the source objects and conventions; minima and optimizer sets are constructed and real conversions require finite objectives
--   - generalization: measurable regression estimates and optimal selections → outer probabilities permit arbitrary selections satisfying the same optimality equalities; reason: all probability bounds follow from pathwise containment in the displayed measurable bounding events; measurable source selections are included
--   - correction: radius (10) prints log(c₁/α) in κ^(2) → reuse the published radius with log(2c₁/α); reason: p. 15 states that Lemma 2 is inverted at α/2; this is the published base correction and is not re-audited here
--   - generalization: the observations follow the joint covariate/error model and the regression estimate is constructed from the first n observations → the reduced interface retains support, the conditional response law and the displayed statistical assumptions, without requiring a joint training-covariate law, covariate/error independence or dependence of the estimator only on the first n observations; reason: the estimates below use only the explicit statistical predicates and pathwise residual/projection identities; every source data model supplies this interface, so no source instance is excluded
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Mathematical Programming (2023), accepted manuscript, https://doi.org/10.1007/s10107-023-02014-7, p. 42, Lemma 24

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Supplement_Infinity

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Wass.Supplement

/-- Full source conclusion, at a fixed covariate satisfying the almost-everywhere hypotheses; sample sizes start at one. -/
theorem lemma_24
    {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model dx dy dz Ω) (P : Measure Ω) (x : E dx)
    (p a c₁ c₂ : ℝ) (κ : ℕ → ℝ → ℝ) (α : ℕ → ℝ)
    (h : WAssumptions M P x p a c₁ c₂ κ α)
    (Q : ℕ → Ω → Measure (E dy))
    (hQ : ∀ n, 1 ≤ n → ∀ ω, Q n ω ∈ WassersteinDRO.Duality.ambiguitySet
      (radii κ p a c₁ c₂ dy α n) p M.D.𝒴 (PER M x n ω)) :
    (∀ n, 1 ≤ n → ENNReal.ofReal (1 - α n) ≤ P {ω |
      WassersteinDRO.Duality.wassersteinDistance p (law M x) (Q n ω) ≤
        ENNReal.ofReal (2 * radii κ p a c₁ c₂ dy α n)}) ∧
    (∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      WassersteinDRO.Duality.wassersteinDistance p (law M x) (Q n ω) ≤
        ENNReal.ofReal (2 * radii κ p a c₁ c₂ dy α n)) ∧
    (∀ᵐ ω ∂P, Tendsto (fun n =>
      WassersteinDRO.Duality.wassersteinDistance p (law M x) (Q n ω)) atTop (𝓝 0)) := by sorry

end ResidualsDRO.Wass.Supplement
