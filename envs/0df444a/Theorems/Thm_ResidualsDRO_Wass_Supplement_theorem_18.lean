-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_Supplement_theorem_18
-- name    : ResidualsDRO.Wass.Supplement.theorem_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:44:36.376151+00:00
-- url     : https://prove2.me/theorems/78954ab1-3ac4-46d6-958b-59dafb69e5c2
-- title:
--   Theorem 18 (corrected: source/boundary conventions) — mean rates
-- statement:
--   Let 1≤q≤∞ and let 0<r≤1 be the rate in Assumption 17. Suppose Assumptions 9, 17 and 18 hold, Assumption 16 holds with ρ=1+r, and the covariate-dependent scenario radius satisfies, for a constant Cμ>0,
--
--   $$\|\mu_n(X)\|_{L^q}=C_\mu n^{-r/2}.$$
--
--   For the unified ER-DRO model with probability sets and radii depending on x, and for any optimal selection, the two mean convergence rates are
--
--   $$\|\widehat v_n(X)-v^*(X)\|_{L^q}=O_p(n^{-r/2}),\qquad\|g(\widehat z_n(X);X)-v^*(X)\|_{L^q}=O_p(n^{-r/2}).$$
--
--   The norm is over P_X with training data fixed, including the essential supremum when q=∞. The radius assumption is equality, not merely an upper bound. The prediction-error rate in Assumption 17 is unsquared, while its training-error rate is for squared errors. This item covers the full covariate-dependent family.
--
--   Differences from the source:
--
--   - encoding: positive sample sizes and almost-everywhere covariates in the Euclidean ER-DRO model → Fin n with n≥1 and a fixed covariate satisfying Standing; extended nonnegative errors, probability tails and full Lq including q=∞; reason: these are the source objects and conventions; minima and optimizer sets are constructed and real conversions require finite objectives
--   - generalization: measurable regression estimates and optimal selections → outer probabilities permit arbitrary selections satisfying the same optimality equalities; reason: all probability bounds follow from pathwise containment in the displayed measurable bounding events; measurable source selections are included
--   - correction: Assumption 12 or 16 has positive squared-simplex equality for every n → the literal equality is required for all sufficiently large n; reason: at n=1 the simplex is {(1)} and its squared deviation is zero; the source convergence arguments are asymptotic, pp. 21, 23, 25
--   - generalization: a family of probability sets parameterized by radius with limit (9) → nonempty simplex-valued sets along the sequence, with the required Assumption 12/16 equality, without prescribing unused off-sequence sets; reason: the proof and conclusions only use these sets along the sequence; every source family gives such a sequence
--   - generalization: the observations follow the joint covariate/error model and the regression estimate is constructed from the first n observations → the reduced interface retains support, the conditional response law and the displayed statistical assumptions, without requiring a joint training-covariate law, covariate/error independence or dependence of the estimator only on the first n observations; reason: the estimates below use only the explicit statistical predicates and pathwise residual/projection identities; every source data model supplies this interface, so no source instance is excluded
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Mathematical Programming (2023), accepted manuscript, https://doi.org/10.1007/s10107-023-02014-7, p. 25, Theorem 18

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Supplement_Infinity

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Wass.Supplement

/-- Full source conclusion, at a fixed covariate satisfying the almost-everywhere hypotheses; sample sizes start at one. -/
theorem theorem_18
    {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model dx dy dz Ω) (P : Measure Ω)
    (ps : E dx → (n : ℕ) → Set (Fin n → ℝ)) (μ : E dx → ℕ → ℝ)
    (q : ℝ≥0∞) (hq : 1 ≤ q) (r Cζ Cμ : ℝ) (hCμ : 0 < Cμ)
    (h : ∀ᵐ x ∂M.PX, Standing M P x ∧ URegular M ps μ x)
    (L : E dz → ℝ) (h9 : Unified.Assumption9 M.c M.D.𝒴 M.Z L)
    (h16 : A16 M ps Cζ (1 + r)) (h17 : A17 M P q r) (h18 : A18 M P q)
    (hμ : ∀ n, 1 ≤ n → lq M q (fun x => μ x n) =
      ENNReal.ofReal (Cμ * (n : ℝ) ^ (-r / 2)))
    (zhat : ℕ → Ω → E dx → E dz)
    (hz : ∀ᵐ x ∂M.PX, ∀ n, 1 ≤ n → ∀ ω, zhat n ω x ∈ usolutions M ps μ x n ω) :
    Unified.IsBigOp P (fun n ω => lq M q (fun x => uvalue M ps μ x n ω - vstar M x))
      (fun n => (n : ℝ) ^ (-r / 2)) ∧
    Unified.IsBigOp P (fun n ω => lq M q (fun x => g M x (zhat n ω x) - vstar M x))
      (fun n => (n : ℝ) ^ (-r / 2)) := by sorry

end ResidualsDRO.Wass.Supplement
