-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_addBlockToSum_fst_bfab06e1e6b8
-- name    : P2M_GroundTheory_Heights__Heights_addBlockToSum_fst_bfab06e1e6b8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:40:36.402466+00:00
-- url     : https://prove2.me/theorems/3acd73af-4d78-4740-9094-8c37d3890a7a
-- title:
--   P2 M Ground Theory Heights  Heights add Block To Sum fst bfab06e1e6b8: P2 M Ground Theory Heights  Heights add Block To Sum fst bfab06e1e6b8
-- statement:
--   The P2 M Ground Theory Heights  Heights add Block To Sum fst bfab06e1e6b8 construction uses the P2 M Ground Theory Heights  Heights add Block To Sum fst bfab06e1e6b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L156-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L156-L158

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

theorem P2M_GroundTheory_Heights__Heights_addBlockToSum_fst_bfab06e1e6b8 (q : Σ o, addBlockIdx ι κ o) :
    (addBlockIdxEquiv q).1 = addBlockToSum q.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«addBlockToSum_fst» := P2M_GroundTheory_Heights__Heights_addBlockToSum_fst_bfab06e1e6b8
