-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMassCompact_mdisc_coord_zero_b76457691cde
-- name    : P2M_GroundTheory_Heights__Heights_ChartMassCompact_mdisc_coord_zero_b76457691cde
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:34.81487+00:00
-- url     : https://prove2.me/theorems/70d8f999-e93c-4d02-91ff-26dcd6afe850
-- title:
--   P2 M Ground Theory Heights  Heights Chart Mass Compact mdisc coord zero b76457691cde: P2 M Ground Theory Heights  Heights Chart Mass Compact mdisc coord zero b76457691cde
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Mass Compact mdisc coord zero b76457691cde construction uses the P2 M Ground Theory Heights  Heights Chart Mass Compact mdisc coord zero b76457691cde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartMassCompact.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartMassCompact.lean#L21-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
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
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMassCompact
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartMassCompact_mdisc_coord_zero_b76457691cde {D : ℕ} (M : Fin D → Matrix (Fin D) (Fin D) ℂ) (i : Fin D)
    (hi : M i = 0) : ReciprocityTheory.AnForm.mdisc M = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMassCompact».«mdisc_coord_zero» := P2M_GroundTheory_Heights__Heights_ChartMassCompact_mdisc_coord_zero_b76457691cde
