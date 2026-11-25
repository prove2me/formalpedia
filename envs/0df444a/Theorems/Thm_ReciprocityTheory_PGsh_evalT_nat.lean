-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_evalT_nat
-- name    : ReciprocityTheory.PGsh.evalT_nat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:09:25.567984+00:00
-- url     : https://prove2.me/theorems/e5c68a24-869a-51a6-a6d6-7ed2e6cfc740
-- title:
--   PGsh: eval T nat
-- statement:
--   The PGsh construction uses the eval T nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L278-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L278-L287

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

theorem ReciprocityTheory.PGsh.evalT_nat {A C : Type u} [CommRing A] [Algebra R₀ A] [CommRing C] [Algebra R₀ C]
    (ρ : A →ₐ[R₀] C) (H : M →ₗ[R₀] A) (K : Submodule R₀ A) (K' : Submodule R₀ C)
    (hK : ∀ a ∈ K, ρ.toLinearMap a ∈ K') (Y : M ⊗[R₀] K) :
    ρ (evalT H K Y) = evalT (ρ.toLinearMap ∘ₗ H) K' (LinearMap.lTensor M (ρ.toLinearMap.restrict hK) Y) := by sorry
