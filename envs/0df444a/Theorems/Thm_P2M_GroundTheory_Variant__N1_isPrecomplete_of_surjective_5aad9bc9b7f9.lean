-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_isPrecomplete_of_surjective_5aad9bc9b7f9
-- name    : P2M_GroundTheory_Variant__N1_isPrecomplete_of_surjective_5aad9bc9b7f9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:49.662096+00:00
-- url     : https://prove2.me/theorems/e548fa4d-40da-5ed3-ba54-87269b246026
-- title:
--   P2 M Ground Theory Variant  N1 is Precomplete of surjective 5aad9bc9b7f9: P2 M Ground Theory Variant  N1 is Precomplete of surjective 5aad9bc9b7f9
-- statement:
--   The P2 M Ground Theory Variant  N1 is Precomplete of surjective 5aad9bc9b7f9 construction uses the P2 M Ground Theory Variant  N1 is Precomplete of surjective 5aad9bc9b7f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/PrecompleteOfSurjective.lean#L10-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/PrecompleteOfSurjective.lean#L10-L45

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_PrecompleteOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1

theorem P2M_GroundTheory_Variant__N1_isPrecomplete_of_surjective_5aad9bc9b7f9 {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (a : A) [IsPrecomplete (Ideal.span {a}) A] :
    IsPrecomplete (Ideal.span {f a}) B := by sorry

alias «GroundTheory».«Variant₂».«N1».«isPrecomplete_of_surjective» := P2M_GroundTheory_Variant__N1_isPrecomplete_of_surjective_5aad9bc9b7f9
