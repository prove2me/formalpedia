-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_ratsInReal_of_mem_locPrimeTo_5ce87b3c663b
-- name    : P2M_GroundTheory_Heights__Heights_mem_ratsInReal_of_mem_locPrimeTo_5ce87b3c663b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:48:05.920807+00:00
-- url     : https://prove2.me/theorems/e9a7b27f-4773-4fe6-8c83-4032f72a31b2
-- title:
--   P2 M Ground Theory Heights  Heights mem rats In Real of mem loc Prime To 5ce87b3c663b: P2 M Ground Theory Heights  Heights mem rats In Real of mem loc Prime To 5ce87b3c663b
-- statement:
--   The P2 M Ground Theory Heights  Heights mem rats In Real of mem loc Prime To 5ce87b3c663b construction uses the P2 M Ground Theory Heights  Heights mem rats In Real of mem loc Prime To 5ce87b3c663b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L183-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L183-L193

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
open IndefiniteRowSideFullHecke.Antisym

theorem P2M_GroundTheory_Heights__Heights_mem_ratsInReal_of_mem_locPrimeTo_5ce87b3c663b {u : ℝ} (hu : u ∈ locPrimeTo chartOne 2) :
    u ∈ ratsInReal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_ratsInReal_of_mem_locPrimeTo» := P2M_GroundTheory_Heights__Heights_mem_ratsInReal_of_mem_locPrimeTo_5ce87b3c663b
