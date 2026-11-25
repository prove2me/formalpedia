-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_summable_gauss
-- name    : ReciprocityTheory.PTheta.sphereQuadraticPositivity.summable_gauss
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:47.936877+00:00
-- url     : https://prove2.me/theorems/cc4edad7-5a4a-4172-82e8-b80ae29a86aa
-- title:
--   sphere Quadratic Positivity: summable gauss
-- statement:
--   The sphere Quadratic Positivity construction uses the summable gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L237-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L237-L253

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

theorem ReciprocityTheory.PTheta.sphereQuadraticPositivity.summable_gauss (β C : ℝ) (hβ : 0 < β) :
    Summable (fun k : ℤ => Real.exp (-(β / 4) * (k : ℝ) ^ 2 + C)) := by sorry
