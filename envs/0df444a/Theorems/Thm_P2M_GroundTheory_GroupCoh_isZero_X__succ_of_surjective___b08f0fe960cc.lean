-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_isZero_X__succ_of_surjective___b08f0fe960cc
-- name    : P2M_GroundTheory_GroupCoh_isZero_X__succ_of_surjective___b08f0fe960cc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:53.542698+00:00
-- url     : https://prove2.me/theorems/6fa7a487-ce84-4f2b-af2d-341610f76f49
-- title:
--   P2 M Ground Theory Group Coh is Zero X  succ of surjective   b08f0fe960cc: P2 M Ground Theory Group Coh is Zero X  succ of surjective   b08f0fe960cc
-- statement:
--   The P2 M Ground Theory Group Coh is Zero X  succ of surjective   b08f0fe960cc construction uses the P2 M Ground Theory Group Coh is Zero X  succ of surjective   b08f0fe960cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L55-L60

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
variable {k H : Type u} [CommRing k] [Group H] {X : ShortComplex (Rep.{u} k H)} (hX : X.ShortExact)
include hX

theorem P2M_GroundTheory_GroupCoh_isZero_X__succ_of_surjective___b08f0fe960cc (n : ℕ) (h₃ : IsZero (groupCohomology X.X₃ (n + 1)))
    (hδ : Function.Surjective (δ hX n (n + 1) rfl)) : IsZero (groupCohomology X.X₂ (n + 1)) := by sorry

alias «GroundTheory».«GroupCoh».«isZero_X₂_succ_of_surjective_δ» := P2M_GroundTheory_GroupCoh_isZero_X__succ_of_surjective___b08f0fe960cc
