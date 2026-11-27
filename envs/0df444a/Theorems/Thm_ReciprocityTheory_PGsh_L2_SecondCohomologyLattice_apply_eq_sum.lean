-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_SecondCohomologyLattice_apply_eq_sum
-- name    : ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.apply_eq_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:48.039802+00:00
-- url     : https://prove2.me/theorems/519ea4fc-798a-471d-9e37-5f56f5cd0b4e
-- title:
--   Second Cohomology Lattice: apply eq sum
-- statement:
--   The Second Cohomology Lattice construction uses the apply eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MapTensorSpan.lean#L83-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MapTensorSpan.lean#L83-L91

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_MapTensorSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.apply_eq_sum {X : Type} [Fintype X] [DecidableEq X] (E : (X → C) →ₗ[C] (X → C))
    (f : X → C) (y : X) :
    E f y = ∑ a, f a * E (fun j => if a = j then 1 else 0) y := by sorry
