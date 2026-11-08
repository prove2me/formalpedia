-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_weightReductionInverseMap1_transpose_basis_weight_le
-- name    : QEC.Coding.FiberBundle.weightReductionInverseMap1_transpose_basis_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:17:06.356308+00:00
-- url     : https://prove2.me/theorems/9720cedf-3eae-4dbf-a36a-08f0048e429c
-- title:
--   Fiber Bundle: weight Reduction Inverse Map1 transpose basis weight le
-- statement:
--   The Fiber Bundle construction uses the weight Reduction Inverse Map1 transpose basis weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L561-L594
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L561-L594

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D

theorem QEC.Coding.FiberBundle.weightReductionInverseMap1_transpose_basis_weight_le
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {L : Nat} (hOne : 1 ≤ L)
    (hCheckDegree : ∀ c : baseZero,
      Fintype.card (ClassicalWeightReduction.CheckNeighbor R c) ≤ L)
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    HammingWeight
        (wordLinearMapTranspose (weightReductionInverseMap1 D h)
          (reducedQubitBasisWord D q)) ≤ L := by sorry
