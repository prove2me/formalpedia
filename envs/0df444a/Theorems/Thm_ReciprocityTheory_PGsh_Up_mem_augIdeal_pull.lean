-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_mem_augIdeal_pull
-- name    : ReciprocityTheory.PGsh.Up.mem_augIdeal_pull
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:57.20016+00:00
-- url     : https://prove2.me/theorems/d59c8c37-15eb-4e6d-8d43-cf08ce39a14f
-- title:
--   Up: mem aug Ideal pull
-- statement:
--   The Up construction uses the mem aug Ideal pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/PrimeHopfOrderOfAddEquiv.lean#L103-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/PrimeHopfOrderOfAddEquiv.lean#L103-L108

import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]

theorem ReciprocityTheory.PGsh.Up.mem_augIdeal_pull (e : X ≃+ Y) (A : HopfOrder (C := C) R Y) (f : X → C) :
    f ∈ augIdeal (hopfPull e A).carrier ↔ (pbE (C := C) (R := R) e).symm f ∈ augIdeal A.carrier := by sorry
