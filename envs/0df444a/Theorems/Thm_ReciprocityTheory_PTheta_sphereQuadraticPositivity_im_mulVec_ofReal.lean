-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_im_mulVec_ofReal
-- name    : ReciprocityTheory.PTheta.sphereQuadraticPositivity.im_mulVec_ofReal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:09:31.993875+00:00
-- url     : https://prove2.me/theorems/e2161611-3ba5-4a1f-838d-55b0c0dad462
-- title:
--   sphere Quadratic Positivity: im mul Vec of Real
-- statement:
--   The sphere Quadratic Positivity construction uses the im mul Vec of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L171-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L171-L174

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

theorem ReciprocityTheory.PTheta.sphereQuadraticPositivity.im_mulVec_ofReal (τ : Matrix ι ι ℂ) (v : ι → ℝ) :
    (fun i => ((τ *ᵥ ofRealVec v) i).im) = τ.map Complex.im *ᵥ v := by sorry
