-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_isZero_X__of_injective___4a150f60598f
-- name    : P2M_GroundTheory_GroupCoh_isZero_X__of_injective___4a150f60598f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:56.233829+00:00
-- url     : https://prove2.me/theorems/79f85de8-97fa-4219-ae18-5e18a3884362
-- title:
--   P2 M Ground Theory Group Coh is Zero X  of injective   4a150f60598f: P2 M Ground Theory Group Coh is Zero X  of injective   4a150f60598f
-- statement:
--   The P2 M Ground Theory Group Coh is Zero X  of injective   4a150f60598f construction uses the P2 M Ground Theory Group Coh is Zero X  of injective   4a150f60598f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L45-L51

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

theorem P2M_GroundTheory_GroupCoh_isZero_X__of_injective___4a150f60598f (n : ℕ) (h₁ : IsZero (groupCohomology X.X₁ n))
    (hδ : Function.Injective (δ hX n (n + 1) rfl)) : IsZero (groupCohomology X.X₂ n) := by sorry

alias «GroundTheory».«GroupCoh».«isZero_X₂_of_injective_δ» := P2M_GroundTheory_GroupCoh_isZero_X__of_injective___4a150f60598f
