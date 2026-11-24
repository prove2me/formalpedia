-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_im_arg
-- name    : ReciprocityTheory.PTheta.sphereQuadraticPositivity.im_arg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:07.561543+00:00
-- url     : https://prove2.me/theorems/1987c1bd-a9fd-46f5-a647-993580c73999
-- title:
--   sphere Quadratic Positivity: im arg
-- statement:
--   The sphere Quadratic Positivity construction uses the im arg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L176-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L176-L184

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

theorem ReciprocityTheory.PTheta.sphereQuadraticPositivity.im_arg (a b : ι → ℝ) (z : ι → ℂ) (τ : Matrix ι ι ℂ) (l : ι → ℤ) :
    (shiftVec a l ⬝ᵥ (τ *ᵥ shiftVec a l) / 2 + shiftVec a l ⬝ᵥ (z + ofRealVec b)).im =
      (fun i => (l i : ℝ) + a i) ⬝ᵥ (τ.map Complex.im *ᵥ (fun i => (l i : ℝ) + a i)) / 2 +
        (fun i => (l i : ℝ) + a i) ⬝ᵥ (fun i => (z i).im) := by sorry
