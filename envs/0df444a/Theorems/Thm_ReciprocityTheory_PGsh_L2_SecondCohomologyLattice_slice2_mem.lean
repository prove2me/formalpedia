-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_SecondCohomologyLattice_slice2_mem
-- name    : ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.slice2_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:38.141591+00:00
-- url     : https://prove2.me/theorems/1ac6796b-2ee7-5111-9178-e3d446eeb70a
-- title:
--   Second Cohomology Lattice: slice2 mem
-- statement:
--   The Second Cohomology Lattice construction uses the slice2 mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MapTensorSpan.lean#L69-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MapTensorSpan.lean#L69-L81

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

theorem ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.slice2_mem {X : Type} (E : (X → C) →ₗ[C] (X → C)) (M M' : Submodule R (X → C))
    (hM : ∀ f ∈ M, E f ∈ M') {F : X × X → C} (hF : F ∈ tensorSpan R M) :
    slice2 E F ∈ tensorSpan R M' := by sorry
