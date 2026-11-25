-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChart_proof_e6b2c0a245fc
-- name    : P2M_GroundTheory_Heights__Heights_SegreChart_proof_e6b2c0a245fc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:39:39.182894+00:00
-- url     : https://prove2.me/theorems/bc847da0-b6ca-57dc-8a4c-2f95cfc44107
-- title:
--   P2 M Ground Theory Heights  Heights Segre Chart proof e6b2c0a245fc: P2 M Ground Theory Heights  Heights Segre Chart proof e6b2c0a245fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Chart proof e6b2c0a245fc construction uses the P2 M Ground Theory Heights  Heights Segre Chart proof e6b2c0a245fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChart.lean#L36-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChart.lean#L36-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isOpen_blockNonzero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Filter Topology
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre isOpen_blockNonzero)

theorem P2M_GroundTheory_Heights__Heights_SegreChart_proof_e6b2c0a245fc (hDim : SegreChartDim.Statement) (hInt : SegreChartIntegral.Statement) :
    SegreChart.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegreChart».«proof» := P2M_GroundTheory_Heights__Heights_SegreChart_proof_e6b2c0a245fc
