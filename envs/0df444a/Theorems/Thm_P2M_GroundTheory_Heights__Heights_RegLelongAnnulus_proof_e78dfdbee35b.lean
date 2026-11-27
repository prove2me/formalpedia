-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_proof_e78dfdbee35b
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_proof_e78dfdbee35b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:35:27.2243+00:00
-- url     : https://prove2.me/theorems/56b0abc1-a527-5e06-a2c7-391b61ca85f8
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus proof e78dfdbee35b: P2 M Ground Theory Heights  Heights Reg Lelong Annulus proof e78dfdbee35b
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus proof e78dfdbee35b construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus proof e78dfdbee35b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L536-L709
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L536-L709

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_proof_477bb4961448
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModelProper_proof_63b250feae60
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
open RegLelongAnnulus

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_proof_e78dfdbee35b (hRW : RegRadialWeight.Statement) (hCM : ChartMassCompact.Statement) :
    RegLelongAnnulus.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«proof» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_proof_e78dfdbee35b
