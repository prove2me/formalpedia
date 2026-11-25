-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_addBlockPullback_of_chartBundlePullback_af7b4b77c248
-- name    : P2M_GroundTheory_Heights__Heights_addBlockPullback_of_chartBundlePullback_af7b4b77c248
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:29.186598+00:00
-- url     : https://prove2.me/theorems/4634a96b-9b7b-4e05-8828-3e062bccd3a7
-- title:
--   P2 M Ground Theory Heights  Heights add Block Pullback of chart Bundle Pullback af7b4b77c248: P2 M Ground Theory Heights  Heights add Block Pullback of chart Bundle Pullback af7b4b77c248
-- statement:
--   The P2 M Ground Theory Heights  Heights add Block Pullback of chart Bundle Pullback af7b4b77c248 construction uses the P2 M Ground Theory Heights  Heights add Block Pullback of chart Bundle Pullback af7b4b77c248 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L124-L127

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
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
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type}

theorem P2M_GroundTheory_Heights__Heights_addBlockPullback_of_chartBundlePullback_af7b4b77c248 (h : ChartBundlePullback.Statement) :
    IndefiniteRowSideFullHecke.Antisym.AddBlockPullback.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«addBlockPullback_of_chartBundlePullback» := P2M_GroundTheory_Heights__Heights_addBlockPullback_of_chartBundlePullback_af7b4b77c248
