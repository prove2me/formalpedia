-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarIntChartChange_proof_0ec19eac3500
-- name    : P2M_GroundTheory_Heights__Heights_VarIntChartChange_proof_0ec19eac3500
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:13.647745+00:00
-- url     : https://prove2.me/theorems/2b48ec5a-6196-4c17-9770-9bbde46c71d7
-- title:
--   P2 M Ground Theory Heights  Heights Var Int Chart Change proof 0ec19eac3500: P2 M Ground Theory Heights  Heights Var Int Chart Change proof 0ec19eac3500
-- statement:
--   The P2 M Ground Theory Heights  Heights Var Int Chart Change proof 0ec19eac3500 construction uses the P2 M Ground Theory Heights  Heights Var Int Chart Change proof 0ec19eac3500 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntChartChange.lean#L171-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntChartChange.lean#L171-L189

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntChartChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeSheetNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntChartChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_proof_4b5bf5e5d261
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PosPartSplit_proof_e6248afef178
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
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
open ChartChange

theorem P2M_GroundTheory_Heights__Heights_VarIntChartChange_proof_0ec19eac3500 (hN : ComplexSets.LinearNoetherNormalization.Statement)
    (hNull : ChartChangeSheetNull.Statement) (hL : ChartChangeLocal.Statement) :
    VarIntChartChange.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarIntChartChange».«proof» := P2M_GroundTheory_Heights__Heights_VarIntChartChange_proof_0ec19eac3500
