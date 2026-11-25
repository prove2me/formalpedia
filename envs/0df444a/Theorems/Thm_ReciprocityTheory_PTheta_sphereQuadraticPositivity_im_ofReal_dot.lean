-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_im_ofReal_dot
-- name    : ReciprocityTheory.PTheta.sphereQuadraticPositivity.im_ofReal_dot
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:09:18.556374+00:00
-- url     : https://prove2.me/theorems/b77d27be-f2d3-5358-b600-6cdae26d669d
-- title:
--   sphere Quadratic Positivity: im of Real dot
-- statement:
--   The sphere Quadratic Positivity construction uses the im of Real dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L167-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L167-L169

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

theorem ReciprocityTheory.PTheta.sphereQuadraticPositivity.im_ofReal_dot (v : ι → ℝ) (w : ι → ℂ) :
    (ofRealVec v ⬝ᵥ w).im = v ⬝ᵥ (fun i => (w i).im) := by sorry
