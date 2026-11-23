-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_evalT_tmul
-- name    : ReciprocityTheory.PGsh.evalT_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:49.213485+00:00
-- url     : https://prove2.me/theorems/80e1f48b-1f82-40aa-8e71-905b4dc8b610
-- title:
--   PGsh: eval T tmul
-- statement:
--   The PGsh construction uses the eval T tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L264-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L264-L266

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

theorem ReciprocityTheory.PGsh.evalT_tmul {A : Type u} [CommRing A] [Algebra R₀ A] (H : M →ₗ[R₀] A) (K : Submodule R₀ A)
    (g : M) (k : K) : evalT H K (g ⊗ₜ k) = H g * k := by sorry
