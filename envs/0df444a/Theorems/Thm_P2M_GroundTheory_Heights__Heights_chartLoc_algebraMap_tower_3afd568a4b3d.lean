-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLoc_algebraMap_tower_3afd568a4b3d
-- name    : P2M_GroundTheory_Heights__Heights_chartLoc_algebraMap_tower_3afd568a4b3d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:18.793264+00:00
-- url     : https://prove2.me/theorems/c2ae5ba1-cab9-4be6-80bf-1fa09d9e4105
-- title:
--   P2 M Ground Theory Heights  Heights chart Loc algebra Map tower 3afd568a4b3d: P2 M Ground Theory Heights  Heights chart Loc algebra Map tower 3afd568a4b3d
-- statement:
--   The P2 M Ground Theory Heights  Heights chart Loc algebra Map tower 3afd568a4b3d construction uses the P2 M Ground Theory Heights  Heights chart Loc algebra Map tower 3afd568a4b3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L17-L20

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

theorem P2M_GroundTheory_Heights__Heights_chartLoc_algebraMap_tower_3afd568a4b3d (x : MvPolynomial (Fin e × Fin n) F) :
    algebraMap (Localization.AtPrime p) (ChartLoc I t e p) (algebraMap _ _ x) =
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chartLoc_algebraMap_tower» := P2M_GroundTheory_Heights__Heights_chartLoc_algebraMap_tower_3afd568a4b3d
