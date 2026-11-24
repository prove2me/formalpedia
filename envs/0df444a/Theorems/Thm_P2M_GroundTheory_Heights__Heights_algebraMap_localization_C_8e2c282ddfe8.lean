-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_algebraMap_localization_C_8e2c282ddfe8
-- name    : P2M_GroundTheory_Heights__Heights_algebraMap_localization_C_8e2c282ddfe8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:47.475794+00:00
-- url     : https://prove2.me/theorems/f393244b-52ee-4d59-83c1-49461325baa6
-- title:
--   P2 M Ground Theory Heights  Heights algebra Map localization C 8e2c282ddfe8: P2 M Ground Theory Heights  Heights algebra Map localization C 8e2c282ddfe8
-- statement:
--   The P2 M Ground Theory Heights  Heights algebra Map localization C 8e2c282ddfe8 construction uses the P2 M Ground Theory Heights  Heights algebra Map localization C 8e2c282ddfe8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L27-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormOfDividedForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartNorm
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
noncomputable section
variable {F : Type} [Field F] {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
  (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_algebraMap_localization_C_8e2c282ddfe8 (c : F) :
    algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p) (C c) =
      algebraMap F (Localization.AtPrime p) c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«algebraMap_localization_C» := P2M_GroundTheory_Heights__Heights_algebraMap_localization_C_8e2c282ddfe8
