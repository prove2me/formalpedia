-- Prove2me | Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_a79258a1bcaa
-- name    : P2M_GlobalTheory_hochschildD__trivialCoaction_a79258a1bcaa
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:07:14.304978+00:00
-- url     : https://prove2.me/theorems/933c77a1-3632-5c19-a1e0-ad906b22d261
-- title:
--   P2 M Global Theory hochschild D  trivial Coaction a79258a1bcaa: P2 M Global Theory hochschild D  trivial Coaction a79258a1bcaa
-- statement:
--   The P2 M Global Theory hochschild D  trivial Coaction a79258a1bcaa construction uses the P2 M Global Theory hochschild D  trivial Coaction a79258a1bcaa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L177-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L177-L180

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

theorem P2M_GlobalTheory_hochschildD__trivialCoaction_a79258a1bcaa : hochschildD₁ (trivialCoaction R H M) =
    (TensorProduct.mk R H H 1).lTensor M - (comul (R := R)).lTensor M +
      ((TensorProduct.mk R H H).flip 1).lTensor M := by sorry

alias «GlobalTheory».«hochschildD₁_trivialCoaction» := P2M_GlobalTheory_hochschildD__trivialCoaction_a79258a1bcaa
