-- Prove2me | Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
-- name    : P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:09:11.682978+00:00
-- url     : https://prove2.me/theorems/8df41348-0c34-49c6-86f5-9f1c893bb290
-- title:
--   P2 M Global Theory hochschild D  trivial Coaction d0af9f793cf0: P2 M Global Theory hochschild D  trivial Coaction d0af9f793cf0
-- statement:
--   The P2 M Global Theory hochschild D  trivial Coaction d0af9f793cf0 construction uses the P2 M Global Theory hochschild D  trivial Coaction d0af9f793cf0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L174-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L174-L175

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

theorem P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0 : hochschildD₀ (trivialCoaction R H M) = 0 := by sorry

alias «GlobalTheory».«hochschildD₀_trivialCoaction» := P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
