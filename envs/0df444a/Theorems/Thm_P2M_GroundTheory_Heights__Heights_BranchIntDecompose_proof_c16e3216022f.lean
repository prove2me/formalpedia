-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BranchIntDecompose_proof_c16e3216022f
-- name    : P2M_GroundTheory_Heights__Heights_BranchIntDecompose_proof_c16e3216022f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:08:24.565632+00:00
-- url     : https://prove2.me/theorems/fa8c51d7-0a62-4962-a495-d6e332d46a2b
-- title:
--   P2 M Ground Theory Heights  Heights Branch Int Decompose proof c16e3216022f: P2 M Ground Theory Heights  Heights Branch Int Decompose proof c16e3216022f
-- statement:
--   The P2 M Ground Theory Heights  Heights Branch Int Decompose proof c16e3216022f construction uses the P2 M Ground Theory Heights  Heights Branch Int Decompose proof c16e3216022f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchIntDecompose.lean#L14-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchIntDecompose.lean#L14-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchIntDecompose
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchProperAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchChartInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntSumOffHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchIntDecompose
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
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_BranchIntDecompose_proof_c16e3216022f (hPr : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement)
    (hGen : ComplexSets.GenericProjectionFinite.Statement) (hSum : ChartIntSumOffHyperplane.Statement)
    (hBr : BranchChartInt.Statement) : BranchIntDecompose.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BranchIntDecompose».«proof» := P2M_GroundTheory_Heights__Heights_BranchIntDecompose_proof_c16e3216022f
