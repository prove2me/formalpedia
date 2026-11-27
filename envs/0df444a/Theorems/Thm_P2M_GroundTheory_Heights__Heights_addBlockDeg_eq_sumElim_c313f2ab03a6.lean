-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_addBlockDeg_eq_sumElim_c313f2ab03a6
-- name    : P2M_GroundTheory_Heights__Heights_addBlockDeg_eq_sumElim_c313f2ab03a6
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:02.198565+00:00
-- url     : https://prove2.me/theorems/c0196f8a-eef9-4e57-8b6a-47c6a6db3fb1
-- title:
--   P2 M Ground Theory Heights  Heights add Block Deg eq sum Elim c313f2ab03a6: P2 M Ground Theory Heights  Heights add Block Deg eq sum Elim c313f2ab03a6
-- statement:
--   The P2 M Ground Theory Heights  Heights add Block Deg eq sum Elim c313f2ab03a6 construction uses the P2 M Ground Theory Heights  Heights add Block Deg eq sum Elim c313f2ab03a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L168-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L168-L171

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
variable {K : Type} {ι : K → Type} {κ : Type}

theorem P2M_GroundTheory_Heights__Heights_addBlockDeg_eq_sumElim_c313f2ab03a6 (a : K → ℤ) :
    addBlockDeg a = Sum.elim a 0 ∘ addBlockToSum := by sorry

alias «GroundTheory».«Heights₂».«Heights».«addBlockDeg_eq_sumElim» := P2M_GroundTheory_Heights__Heights_addBlockDeg_eq_sumElim_c313f2ab03a6
