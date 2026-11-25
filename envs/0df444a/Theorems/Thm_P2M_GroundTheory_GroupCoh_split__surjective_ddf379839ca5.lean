-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_split__surjective_ddf379839ca5
-- name    : P2M_GroundTheory_GroupCoh_split__surjective_ddf379839ca5
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:58.192789+00:00
-- url     : https://prove2.me/theorems/8de1b693-dd06-422a-8e79-47a34ac31ab3
-- title:
--   P2 M Ground Theory Group Coh split  surjective ddf379839ca5: P2 M Ground Theory Group Coh split  surjective ddf379839ca5
-- statement:
--   The P2 M Ground Theory Group Coh split  surjective ddf379839ca5 construction uses the P2 M Ground Theory Group Coh split  surjective ddf379839ca5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L180-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L180-L185

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
omit [Fintype S]

theorem P2M_GroundTheory_GroupCoh_split__surjective_ddf379839ca5
    (h3 : ∀ y : groupCohomology (res S.subtype M) 2, ∃ m : ℤ, y = m • resClass M u S) :
    Function.Surjective (splitδ M u S) := by sorry

alias «GroundTheory».«GroupCoh».«splitδ_surjective» := P2M_GroundTheory_GroupCoh_split__surjective_ddf379839ca5
