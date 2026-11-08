-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_weightReductionForwardMap1_basis_weight_le
-- name    : QEC.Coding.FiberBundle.weightReductionForwardMap1_basis_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:15:07.754708+00:00
-- url     : https://prove2.me/theorems/6c4475a8-5577-4949-8d4f-4d86dd512ea8
-- title:
--   Fiber Bundle: weight Reduction Forward Map1 basis weight le
-- statement:
--   The Fiber Bundle construction uses the weight Reduction Forward Map1 basis weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L253-L277
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L253-L277

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

theorem QEC.Coding.FiberBundle.weightReductionForwardMap1_basis_weight_le
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {L : Nat} (hOne : 1 ≤ L)
    (hBitDegree : ∀ b : baseOne,
      Fintype.card (ClassicalWeightReduction.BitNeighbor R b) ≤ L)
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    HammingWeight
        (weightReductionForwardMap1 D h (reducedQubitBasisWord D q)) ≤ L := by sorry
