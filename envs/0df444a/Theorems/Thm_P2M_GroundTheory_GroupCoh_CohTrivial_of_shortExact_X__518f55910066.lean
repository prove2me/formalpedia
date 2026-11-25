-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_CohTrivial_of_shortExact_X__518f55910066
-- name    : P2M_GroundTheory_GroupCoh_CohTrivial_of_shortExact_X__518f55910066
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:27:27.975464+00:00
-- url     : https://prove2.me/theorems/baee5f44-83cc-4159-9915-cf79b47bffc9
-- title:
--   P2 M Ground Theory Group Coh Coh Trivial of short Exact X  518f55910066: P2 M Ground Theory Group Coh Coh Trivial of short Exact X  518f55910066
-- statement:
--   The P2 M Ground Theory Group Coh Coh Trivial of short Exact X  518f55910066 construction uses the P2 M Ground Theory Group Coh Coh Trivial of short Exact X  518f55910066 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivialBasic.lean#L139-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivialBasic.lean#L139-L149

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

theorem P2M_GroundTheory_GroupCoh_CohTrivial_of_shortExact_X__518f55910066 {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (h₂ : CohTrivial S.X₂) (h₁ : CohTrivial S.X₁) : CohTrivial S.X₃ := by sorry

alias «GroundTheory».«GroupCoh».«CohTrivial».«of_shortExact_X₁» := P2M_GroundTheory_GroupCoh_CohTrivial_of_shortExact_X__518f55910066
