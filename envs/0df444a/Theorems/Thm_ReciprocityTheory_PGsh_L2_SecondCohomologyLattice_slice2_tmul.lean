-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_SecondCohomologyLattice_slice2_tmul
-- name    : ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.slice2_tmul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:58.953047+00:00
-- url     : https://prove2.me/theorems/bd5a2476-1225-454a-b569-ba0493ae5671
-- title:
--   Second Cohomology Lattice: slice2 tmul
-- statement:
--   The Second Cohomology Lattice construction uses the slice2 tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MapTensorSpan.lean#L48-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MapTensorSpan.lean#L48-L57

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

theorem ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.slice2_tmul {X : Type} (E : (X → C) →ₗ[C] (X → C)) (g h : X → C) :
    slice2 E (fun p => g p.1 * h p.2) = fun p => E g p.1 * E h p.2 := by sorry
