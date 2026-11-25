-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_split__augClass_80c011573ab3
-- name    : P2M_GroundTheory_GroupCoh_split__augClass_80c011573ab3
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:18:02.414083+00:00
-- url     : https://prove2.me/theorems/1578cd33-ff25-5406-9f26-3b503e1344e7
-- title:
--   P2 M Ground Theory Group Coh split  aug Class 80c011573ab3: P2 M Ground Theory Group Coh split  aug Class 80c011573ab3
-- statement:
--   The P2 M Ground Theory Group Coh split  aug Class 80c011573ab3 construction uses the P2 M Ground Theory Group Coh split  aug Class 80c011573ab3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L165-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L165-L166

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

theorem P2M_GroundTheory_GroupCoh_split__augClass_80c011573ab3 : splitδ M u S (augClass S) = resClass M u S := by sorry

alias «GroundTheory».«GroupCoh».«splitδ_augClass» := P2M_GroundTheory_GroupCoh_split__augClass_80c011573ab3
