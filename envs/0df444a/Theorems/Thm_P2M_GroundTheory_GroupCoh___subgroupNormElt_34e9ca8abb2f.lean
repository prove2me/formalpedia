-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh___subgroupNormElt_34e9ca8abb2f
-- name    : P2M_GroundTheory_GroupCoh___subgroupNormElt_34e9ca8abb2f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:38.119128+00:00
-- url     : https://prove2.me/theorems/44dd5141-3b80-4be0-a12a-e439ff5ea538
-- title:
--   P2 M Ground Theory Group Coh   subgroup Norm Elt 34e9ca8abb2f: P2 M Ground Theory Group Coh   subgroup Norm Elt 34e9ca8abb2f
-- statement:
--   The P2 M Ground Theory Group Coh   subgroup Norm Elt 34e9ca8abb2f construction uses the P2 M Ground Theory Group Coh   subgroup Norm Elt 34e9ca8abb2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L116-L119

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
omit [Fintype G]

theorem P2M_GroundTheory_GroupCoh___subgroupNormElt_34e9ca8abb2f (s : S) :
    (Rep.leftRegular ℤ G).ρ (s : G) (subgroupNormElt S) = subgroupNormElt S := by sorry

alias «GroundTheory».«GroupCoh».«ρ_subgroupNormElt» := P2M_GroundTheory_GroupCoh___subgroupNormElt_34e9ca8abb2f
