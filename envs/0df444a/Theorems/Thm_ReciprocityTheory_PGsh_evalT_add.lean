-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_evalT_add
-- name    : ReciprocityTheory.PGsh.evalT_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:32.254871+00:00
-- url     : https://prove2.me/theorems/faa0ef11-d297-4e4f-8efd-553c1b1a4e19
-- title:
--   PGsh: eval T add
-- statement:
--   The PGsh construction uses the eval T add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L268-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L268-L271

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

theorem ReciprocityTheory.PGsh.evalT_add {A : Type u} [CommRing A] [Algebra R₀ A] (H : M →ₗ[R₀] A) (K : Submodule R₀ A)
    (Y Y' : M ⊗[R₀] K) : evalT H K (Y + Y') = evalT H K Y + evalT H K Y' := by sorry
