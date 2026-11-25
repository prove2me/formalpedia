-- Prove2me | Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_injective_eee200d99995
-- name    : P2M_GlobalTheory_hochschildD__trivialCoaction_injective_eee200d99995
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:13:29.406169+00:00
-- url     : https://prove2.me/theorems/b9fc30f7-0e03-5125-93ab-68861617071e
-- title:
--   P2 M Global Theory hochschild D  trivial Coaction injective eee200d99995: P2 M Global Theory hochschild D  trivial Coaction injective eee200d99995
-- statement:
--   The P2 M Global Theory hochschild D  trivial Coaction injective eee200d99995 construction uses the P2 M Global Theory hochschild D  trivial Coaction injective eee200d99995 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L297-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L297-L300

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
variable (R M X)

theorem P2M_GlobalTheory_hochschildD__trivialCoaction_injective_eee200d99995 :
    Function.Injective (hochschildD₁ (trivialCoaction R R[X] M)) := by sorry

alias «GlobalTheory».«hochschildD₁_trivialCoaction_injective» := P2M_GlobalTheory_hochschildD__trivialCoaction_injective_eee200d99995
