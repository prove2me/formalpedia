-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMassCompact_proof_637e1cfa7406
-- name    : P2M_GroundTheory_Heights__Heights_ChartMassCompact_proof_637e1cfa7406
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:27:47.866343+00:00
-- url     : https://prove2.me/theorems/161393ab-7311-4ed3-b8f6-512de4be6225
-- title:
--   P2 M Ground Theory Heights  Heights Chart Mass Compact proof 637e1cfa7406: P2 M Ground Theory Heights  Heights Chart Mass Compact proof 637e1cfa7406
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Mass Compact proof 637e1cfa7406 construction uses the P2 M Ground Theory Heights  Heights Chart Mass Compact proof 637e1cfa7406 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartMassCompact.lean#L103-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartMassCompact.lean#L103-L129

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOff_proof_fa25535eea0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1

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
open ChartMassCompact

theorem P2M_GroundTheory_Heights__Heights_ChartMassCompact_proof_637e1cfa7406 (hC : ChartMassCompare.Statement) (hMF : MassFinite.Statement) :
    ChartMassCompact.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMassCompact».«proof» := P2M_GroundTheory_Heights__Heights_ChartMassCompact_proof_637e1cfa7406
