-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_d___mapRange_addEquiv_c46ee4082a24
-- name    : P2M_GroundTheory_GroupCoh_d___mapRange_addEquiv_c46ee4082a24
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:37:32.349796+00:00
-- url     : https://prove2.me/theorems/103d2c59-832a-59e6-9706-cd9f1e645b77
-- title:
--   P2 M Ground Theory Group Coh d   map Range add Equiv c46ee4082a24: P2 M Ground Theory Group Coh d   map Range add Equiv c46ee4082a24
-- statement:
--   The P2 M Ground Theory Group Coh d   map Range add Equiv c46ee4082a24 construction uses the P2 M Ground Theory Group Coh d   map Range add Equiv c46ee4082a24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L42-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L42-L51

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

theorem P2M_GroundTheory_GroupCoh_d___mapRange_addEquiv_c46ee4082a24 (e : A.V ≃+ B.V) (he : ∀ g a, e (A.ρ g a) = B.ρ g (e a))
    (c : G × G →₀ A) :
    d₂₁ B (Finsupp.mapRange e (map_zero e) c) = Finsupp.mapRange e (map_zero e) (d₂₁ A c) := by sorry

alias «GroundTheory».«GroupCoh».«d₂₁_mapRange_addEquiv» := P2M_GroundTheory_GroupCoh_d___mapRange_addEquiv_c46ee4082a24
