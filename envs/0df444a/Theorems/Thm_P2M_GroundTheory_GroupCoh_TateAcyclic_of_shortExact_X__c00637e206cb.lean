-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_TateAcyclic_of_shortExact_X__c00637e206cb
-- name    : P2M_GroundTheory_GroupCoh_TateAcyclic_of_shortExact_X__c00637e206cb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:27:51.22981+00:00
-- url     : https://prove2.me/theorems/cc5984f5-e255-4c91-93c0-8d66a403b464
-- title:
--   P2 M Ground Theory Group Coh Tate Acyclic of short Exact X  c00637e206cb: P2 M Ground Theory Group Coh Tate Acyclic of short Exact X  c00637e206cb
-- statement:
--   The P2 M Ground Theory Group Coh Tate Acyclic of short Exact X  c00637e206cb construction uses the P2 M Ground Theory Group Coh Tate Acyclic of short Exact X  c00637e206cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivialBasic.lean#L115-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivialBasic.lean#L115-L120

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
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
open CategoryTheory Limits Rep
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G]

theorem P2M_GroundTheory_GroupCoh_TateAcyclic_of_shortExact_X__c00637e206cb [Fintype G] {S : ShortComplex (Rep.{u} k G)}
    (hS : S.ShortExact) (h₂ : TateAcyclic S.X₂) (h₃ : TateAcyclic S.X₃) : TateAcyclic S.X₁ := by sorry

alias «GroundTheory».«GroupCoh».«TateAcyclic».«of_shortExact_X₃» := P2M_GroundTheory_GroupCoh_TateAcyclic_of_shortExact_X__c00637e206cb
