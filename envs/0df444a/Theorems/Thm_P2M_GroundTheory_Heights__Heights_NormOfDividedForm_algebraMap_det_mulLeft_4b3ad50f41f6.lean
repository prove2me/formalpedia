-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormOfDividedForm_algebraMap_det_mulLeft_4b3ad50f41f6
-- name    : P2M_GroundTheory_Heights__Heights_NormOfDividedForm_algebraMap_det_mulLeft_4b3ad50f41f6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:04:57.903471+00:00
-- url     : https://prove2.me/theorems/6772c3bc-6887-4279-869a-b0e99cfc3b0f
-- title:
--   P2 M Ground Theory Heights  Heights Norm Of Divided Form algebra Map det mul Left 4b3ad50f41f6: P2 M Ground Theory Heights  Heights Norm Of Divided Form algebra Map det mul Left 4b3ad50f41f6
-- statement:
--   The P2 M Ground Theory Heights  Heights Norm Of Divided Form algebra Map det mul Left 4b3ad50f41f6 construction uses the P2 M Ground Theory Heights  Heights Norm Of Divided Form algebra Map det mul Left 4b3ad50f41f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PNormOfDividedForm.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PNormOfDividedForm.lean#L53-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormOfDividedForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PNormOfDividedForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open scoped nonZeroDivisors
noncomputable section
open GroundTheory.Heights₂.Heights.NormOfDividedForm
variable {O B K L : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B] [Field K] [Field L] [Algebra O K]
  [IsFractionRing O K] [Algebra B L] [Algebra K L] [Algebra O L] [IsScalarTower O K L] [IsScalarTower O B L]
  [IsLocalization (Algebra.algebraMapSubmonoid B O⁰) L]
omit [IsDomain O]

theorem P2M_GroundTheory_Heights__Heights_NormOfDividedForm_algebraMap_det_mulLeft_4b3ad50f41f6 [Module.Free O B] [Module.Finite O B] [FiniteDimensional K L]
    (hEval : NormFormEval.Statement) {n : ℕ} (η : Fin n → B) (v : Fin n → O) :
    algebraMap O K (LinearMap.det (LinearMap.mulLeft O (∑ m, v m • η m))) =
      eval (fun m => algebraMap O K (v m)) (normForm K L fun m => algebraMap B L (η m)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormOfDividedForm».«algebraMap_det_mulLeft» := P2M_GroundTheory_Heights__Heights_NormOfDividedForm_algebraMap_det_mulLeft_4b3ad50f41f6
