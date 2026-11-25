-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_TateAcyclic_of_shortExact_X__8e70e005e54b
-- name    : P2M_GroundTheory_GroupCoh_TateAcyclic_of_shortExact_X__8e70e005e54b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:21:09.064491+00:00
-- url     : https://prove2.me/theorems/f12255ba-39c1-4f37-9eab-7f74a2f5a86f
-- title:
--   P2 M Ground Theory Group Coh Tate Acyclic of short Exact X  8e70e005e54b: P2 M Ground Theory Group Coh Tate Acyclic of short Exact X  8e70e005e54b
-- statement:
--   The P2 M Ground Theory Group Coh Tate Acyclic of short Exact X  8e70e005e54b construction uses the P2 M Ground Theory Group Coh Tate Acyclic of short Exact X  8e70e005e54b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivialBasic.lean#L122-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivialBasic.lean#L122-L125

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

theorem P2M_GroundTheory_GroupCoh_TateAcyclic_of_shortExact_X__8e70e005e54b [Fintype G] {S : ShortComplex (Rep.{u} k G)}
    (hS : S.ShortExact) (h₂ : TateAcyclic S.X₂) (h₁ : TateAcyclic S.X₁) : TateAcyclic S.X₃ := by sorry

alias «GroundTheory».«GroupCoh».«TateAcyclic».«of_shortExact_X₁» := P2M_GroundTheory_GroupCoh_TateAcyclic_of_shortExact_X__8e70e005e54b
