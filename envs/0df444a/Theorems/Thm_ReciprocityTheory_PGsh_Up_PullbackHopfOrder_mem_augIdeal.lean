-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_PullbackHopfOrder_mem_augIdeal
-- name    : ReciprocityTheory.PGsh.Up.PullbackHopfOrder.mem_augIdeal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:06:21.534091+00:00
-- url     : https://prove2.me/theorems/09d76515-7a12-4bdc-9a65-6a25eb985f09
-- title:
--   Pullback Hopf Order: mem aug Ideal
-- statement:
--   The Pullback Hopf Order construction uses the mem aug Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemAugIdeal.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemAugIdeal.lean#L13-L15

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_MemAugIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.PullbackHopfOrder
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.PullbackHopfOrder.mem_augIdeal {X : Type} [AddCommGroup X] {M : Submodule R (X → C)} {f : X → C} :
    f ∈ augIdeal M ↔ f ∈ M ∧ f 0 = 0 := by sorry
