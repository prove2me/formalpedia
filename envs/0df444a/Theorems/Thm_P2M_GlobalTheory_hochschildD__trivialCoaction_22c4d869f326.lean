-- Prove2me | Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_22c4d869f326
-- name    : P2M_GlobalTheory_hochschildD__trivialCoaction_22c4d869f326
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:14:04.834344+00:00
-- url     : https://prove2.me/theorems/70332b57-0cb0-4ce8-ae89-48718982b7b0
-- title:
--   P2 M Global Theory hochschild D  trivial Coaction 22c4d869f326: P2 M Global Theory hochschild D  trivial Coaction 22c4d869f326
-- statement:
--   The P2 M Global Theory hochschild D  trivial Coaction 22c4d869f326 construction uses the P2 M Global Theory hochschild D  trivial Coaction 22c4d869f326 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L182-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L182-L187

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

theorem P2M_GlobalTheory_hochschildD__trivialCoaction_22c4d869f326 : hochschildD₂ (trivialCoaction R H M) =
    (TensorProduct.mk R H (H ⊗[R] H) 1).lTensor M -
      ((TensorProduct.assoc R H H H).toLinearMap ∘ₗ (comul (R := R)).rTensor H).lTensor M +
      ((comul (R := R)).lTensor H).lTensor M -
      (((TensorProduct.mk R H H).flip 1).lTensor H).lTensor M := by sorry

alias «GlobalTheory».«hochschildD₂_trivialCoaction» := P2M_GlobalTheory_hochschildD__trivialCoaction_22c4d869f326
