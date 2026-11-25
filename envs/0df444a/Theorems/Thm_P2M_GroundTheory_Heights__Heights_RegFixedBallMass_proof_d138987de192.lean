-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegFixedBallMass_proof_d138987de192
-- name    : P2M_GroundTheory_Heights__Heights_RegFixedBallMass_proof_d138987de192
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:47:43.37263+00:00
-- url     : https://prove2.me/theorems/b54e0d79-8623-5f93-a452-18817a5ed47e
-- title:
--   P2 M Ground Theory Heights  Heights Reg Fixed Ball Mass proof d138987de192: P2 M Ground Theory Heights  Heights Reg Fixed Ball Mass proof d138987de192
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Fixed Ball Mass proof d138987de192 construction uses the P2 M Ground Theory Heights  Heights Reg Fixed Ball Mass proof d138987de192 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegFixedBallMass.lean#L43-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegFixedBallMass.lean#L43-L111

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegFixedBallMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegDensNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOnChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CutOffNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegBallMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegFixedBallMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_proof_477bb4961448
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOff_proof_fa25535eea0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModelProper_proof_63b250feae60
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_proof_dfe9c2a6cf8c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegBallMass_proof_fdc7e2a04306
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
open scoped ContDiff
noncomputable section
open RegFixedBallMass

theorem P2M_GroundTheory_Heights__Heights_RegFixedBallMass_proof_d138987de192 (hN : RegDensNonneg.Statement) (hS : StokesOnChart.Statement)
    (hL : LogIntegrable.Statement) (hC : ChartMassCompact.Statement) : RegFixedBallMass.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegFixedBallMass».«proof» := P2M_GroundTheory_Heights__Heights_RegFixedBallMass_proof_d138987de192
