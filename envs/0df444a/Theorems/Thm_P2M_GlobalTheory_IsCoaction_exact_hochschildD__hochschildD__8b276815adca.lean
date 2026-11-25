-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IsCoaction_exact_hochschildD__hochschildD__8b276815adca
-- name    : P2M_GlobalTheory_IsCoaction_exact_hochschildD__hochschildD__8b276815adca
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:06:59.969396+00:00
-- url     : https://prove2.me/theorems/5870e212-bddb-491b-bf88-7f1a5d08f6da
-- title:
--   P2 M Global Theory Is Coaction exact hochschild D  hochschild D  8b276815adca: P2 M Global Theory Is Coaction exact hochschild D  hochschild D  8b276815adca
-- statement:
--   The P2 M Global Theory Is Coaction exact hochschild D  hochschild D  8b276815adca construction uses the P2 M Global Theory Is Coaction exact hochschild D  hochschild D  8b276815adca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L270-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L270-L293

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

theorem P2M_GlobalTheory_IsCoaction_exact_hochschildD__hochschildD__8b276815adca {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ) :
    Function.Exact (hochschildD₁ ρ) (hochschildD₂ ρ) := by sorry

alias «GlobalTheory».«IsCoaction».«exact_hochschildD₁_hochschildD₂» := P2M_GlobalTheory_IsCoaction_exact_hochschildD__hochschildD__8b276815adca
