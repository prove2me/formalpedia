-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_shiftVec_eq
-- name    : ReciprocityTheory.PTheta.sphereQuadraticPositivity.shiftVec_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:30.652048+00:00
-- url     : https://prove2.me/theorems/e6cb04eb-7846-549d-b97b-46cc36bbf281
-- title:
--   sphere Quadratic Positivity: shift Vec eq
-- statement:
--   The sphere Quadratic Positivity construction uses the shift Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L162-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L162-L165

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

theorem ReciprocityTheory.PTheta.sphereQuadraticPositivity.shiftVec_eq (a : ι → ℝ) (l : ι → ℤ) :
    shiftVec a l = ofRealVec (fun i => (l i : ℝ) + a i) := by sorry
