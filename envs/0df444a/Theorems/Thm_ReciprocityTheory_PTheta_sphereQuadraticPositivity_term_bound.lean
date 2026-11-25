-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_term_bound
-- name    : ReciprocityTheory.PTheta.sphereQuadraticPositivity.term_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:49.019673+00:00
-- url     : https://prove2.me/theorems/879baed4-0852-52f0-82c5-8e69346c21b5
-- title:
--   sphere Quadratic Positivity: term bound
-- statement:
--   The sphere Quadratic Positivity construction uses the term bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L260-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L260-L298

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta ReciprocityTheory.PTheta.sphereQuadraticPositivity
variable {ι : Type*} [Fintype ι]

theorem ReciprocityTheory.PTheta.sphereQuadraticPositivity.term_bound (a b : ι → ℝ) (z : ι → ℂ) (A : Matrix ι ι ℂ) (l : ι → ℤ) (c R : ℝ)
    (hc0 : 0 < c) (hR0 : 0 ≤ R) (hR : ∀ i, |(z i).im| ≤ R)
    (hq : ∀ x : ι → ℝ, c * ∑ i, x i ^ 2 ≤ x ⬝ᵥ ((A.map Complex.im + (A.map Complex.im)ᵀ) *ᵥ x)) :
    ‖thetaTerm a b z A l‖ ≤ ∏ i, Real.exp (-((Real.pi * c / 2) / 4) * (l i : ℝ) ^ 2 +
      ((2 * Real.pi * R) ^ 2 / (2 * (Real.pi * c / 2)) + (Real.pi * c / 2) / 2 * a i ^ 2)) := by sorry
