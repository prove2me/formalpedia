-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_split__injective_819166473dcc
-- name    : P2M_GroundTheory_GroupCoh_split__injective_819166473dcc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:13.868042+00:00
-- url     : https://prove2.me/theorems/1680b3f7-c892-4373-8f1e-aae3ec095a90
-- title:
--   P2 M Ground Theory Group Coh split  injective 819166473dcc: P2 M Ground Theory Group Coh split  injective 819166473dcc
-- statement:
--   The P2 M Ground Theory Group Coh split  injective 819166473dcc construction uses the P2 M Ground Theory Group Coh split  injective 819166473dcc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L168-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L168-L176

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
variable (S : Subgroup G) [Fintype S]

theorem P2M_GroundTheory_GroupCoh_split__injective_819166473dcc (h2 : addOrderOf (resClass M u S) = Nat.card S) :
    Function.Injective (splitδ M u S) := by sorry

alias «GroundTheory».«GroupCoh».«splitδ_injective» := P2M_GroundTheory_GroupCoh_split__injective_819166473dcc
