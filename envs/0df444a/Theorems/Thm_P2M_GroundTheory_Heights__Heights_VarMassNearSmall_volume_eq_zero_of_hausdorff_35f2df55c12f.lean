-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarMassNearSmall_volume_eq_zero_of_hausdorff_35f2df55c12f
-- name    : P2M_GroundTheory_Heights__Heights_VarMassNearSmall_volume_eq_zero_of_hausdorff_35f2df55c12f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:04.468456+00:00
-- url     : https://prove2.me/theorems/a382466f-4fc4-49a8-bf05-5a081cf412dc
-- title:
--   P2 M Ground Theory Heights  Heights Var Mass Near Small volume eq zero of hausdorff 35f2df55c12f: P2 M Ground Theory Heights  Heights Var Mass Near Small volume eq zero of hausdorff 35f2df55c12f
-- statement:
--   The P2 M Ground Theory Heights  Heights Var Mass Near Small volume eq zero of hausdorff 35f2df55c12f construction uses the P2 M Ground Theory Heights  Heights Var Mass Near Small volume eq zero of hausdorff 35f2df55c12f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarMassNearSmall.lean#L33-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarMassNearSmall.lean#L33-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarMassNearSmall
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal NNReal
noncomputable section
open GroundTheory.Heights₂.Heights.VarMassNearSmall
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_VarMassNearSmall_volume_eq_zero_of_hausdorff_35f2df55c12f {S : Set (Fin d → ℂ)} (hS : μH[((2 * d : ℕ) : ℝ)] S = 0) :
    volume S = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarMassNearSmall».«volume_eq_zero_of_hausdorff» := P2M_GroundTheory_Heights__Heights_VarMassNearSmall_volume_eq_zero_of_hausdorff_35f2df55c12f
