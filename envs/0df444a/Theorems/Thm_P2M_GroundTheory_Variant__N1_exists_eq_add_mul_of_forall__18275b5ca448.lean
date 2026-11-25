-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_eq_add_mul_of_forall__18275b5ca448
-- name    : P2M_GroundTheory_Variant__N1_exists_eq_add_mul_of_forall__18275b5ca448
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:53.406514+00:00
-- url     : https://prove2.me/theorems/4ad87c2b-b927-412c-8738-9cea70cbcae3
-- title:
--   P2 M Ground Theory Variant  N1 exists eq add mul of forall  18275b5ca448: P2 M Ground Theory Variant  N1 exists eq add mul of forall  18275b5ca448
-- statement:
--   The P2 M Ground Theory Variant  N1 exists eq add mul of forall  18275b5ca448 construction uses the P2 M Ground Theory Variant  N1 exists eq add mul of forall  18275b5ca448 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/FontainePhiPowerSubgroups.lean#L21-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/FontainePhiPowerSubgroups.lean#L21-L53

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_FontainePhiPowerSubgroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1

theorem P2M_GroundTheory_Variant__N1_exists_eq_add_mul_of_forall__18275b5ca448 {A : Type*} {R : Type*} {ι : Type*} [CommRing A]
    [CommRing R] {a : A} {r : R} [IsAdicComplete (Ideal.span {a}) A]
    [IsAdicComplete (Ideal.span {r}) R] (f : A →+* R) :
    f a = r →
      ∀ (X : R) (ψ : ι → R),
        (∀ (y : ι), ∃ (b : A) (s : R) (y' : ι), ψ y = f b + X * s + r * ψ y') →
          ∀ (y : ι), ∃ (b : A) (s : R), ψ y = f b + X * s := by sorry

alias «GroundTheory».«Variant₂».«N1».«exists_eq_add_mul_of_forall'» := P2M_GroundTheory_Variant__N1_exists_eq_add_mul_of_forall__18275b5ca448
