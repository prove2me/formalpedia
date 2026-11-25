-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_d___mapRange_addEquiv_855b748d2b6d
-- name    : P2M_GroundTheory_GroupCoh_d___mapRange_addEquiv_855b748d2b6d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:27.306389+00:00
-- url     : https://prove2.me/theorems/d2db88a3-1b40-497e-a824-482afd54d5f8
-- title:
--   P2 M Ground Theory Group Coh d   map Range add Equiv 855b748d2b6d: P2 M Ground Theory Group Coh d   map Range add Equiv 855b748d2b6d
-- statement:
--   The P2 M Ground Theory Group Coh d   map Range add Equiv 855b748d2b6d construction uses the P2 M Ground Theory Group Coh d   map Range add Equiv 855b748d2b6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L35-L40

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivial
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupHomology
universe u
variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G]
variable {A : Rep.{u} k G} {B : Rep.{u} k' G}

theorem P2M_GroundTheory_GroupCoh_d___mapRange_addEquiv_855b748d2b6d (e : A.V ≃+ B.V) (he : ∀ g a, e (A.ρ g a) = B.ρ g (e a))
    (y : G →₀ A) : d₁₀ B (Finsupp.mapRange e (map_zero e) y) = e (d₁₀ A y) := by sorry

alias «GroundTheory».«GroupCoh».«d₁₀_mapRange_addEquiv» := P2M_GroundTheory_GroupCoh_d___mapRange_addEquiv_855b748d2b6d
