-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_evalT_mem
-- name    : ReciprocityTheory.PGsh.evalT_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:36.303819+00:00
-- url     : https://prove2.me/theorems/000779f4-d380-4f34-996e-e4f890b7dc2d
-- title:
--   PGsh: eval T mem
-- statement:
--   The PGsh construction uses the eval T mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L289-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L289-L300

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
variable {M : Type u} [AddCommGroup M] [Module R₀ M]

theorem ReciprocityTheory.PGsh.evalT_mem {A : Type u} [CommRing A] [Algebra R₀ A] (H : M →ₗ[R₀] A) (I : Ideal A)
    (Y : M ⊗[R₀] (I.restrictScalars R₀)) : evalT H (I.restrictScalars R₀) Y ∈ I := by sorry
