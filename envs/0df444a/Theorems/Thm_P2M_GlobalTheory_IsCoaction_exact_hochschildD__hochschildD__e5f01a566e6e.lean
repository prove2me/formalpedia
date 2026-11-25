-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IsCoaction_exact_hochschildD__hochschildD__e5f01a566e6e
-- name    : P2M_GlobalTheory_IsCoaction_exact_hochschildD__hochschildD__e5f01a566e6e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:06:40.659806+00:00
-- url     : https://prove2.me/theorems/11d89c9e-c235-4186-87af-607f297b111e
-- title:
--   P2 M Global Theory Is Coaction exact hochschild D  hochschild D  e5f01a566e6e: P2 M Global Theory Is Coaction exact hochschild D  hochschild D  e5f01a566e6e
-- statement:
--   The P2 M Global Theory Is Coaction exact hochschild D  hochschild D  e5f01a566e6e construction uses the P2 M Global Theory Is Coaction exact hochschild D  hochschild D  e5f01a566e6e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L256-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L256-L268

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TupleDifferentialTupleDifferential
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorCoeffOfMemTorusWeightSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra AddMonoidAlgebra
open GlobalTheory
variable {R : Type*} [CommRing R] {H : Type*} [Ring H] [Bialgebra R H]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {X : Type*} [AddMonoid X]

theorem P2M_GlobalTheory_IsCoaction_exact_hochschildD__hochschildD__e5f01a566e6e {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ) :
    Function.Exact (hochschildD₀ ρ) (hochschildD₁ ρ) := by sorry

alias «GlobalTheory».«IsCoaction».«exact_hochschildD₀_hochschildD₁» := P2M_GlobalTheory_IsCoaction_exact_hochschildD__hochschildD__e5f01a566e6e
