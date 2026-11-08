-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_qubitIndex_weightReduced_le_of_bitDegree
-- name    : QEC.Coding.FiberBundle.card_qubitIndex_weightReduced_le_of_bitDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:25:41.963945+00:00
-- url     : https://prove2.me/theorems/58493d67-4b62-4c03-9e32-7231fa8e9752
-- title:
--   Fiber Bundle: card qubit Index weight Reduced le of bit Degree
-- statement:
--   The Fiber Bundle construction uses the card qubit Index weight Reduced le of bit Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L790-L805
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L790-L805

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u v
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D

theorem QEC.Coding.FiberBundle.card_qubitIndex_weightReduced_le_of_bitDegree
    {L : Nat}
    (hBitDegree : ∀ b : baseOne,
      Fintype.card (ClassicalWeightReduction.BitNeighbor R b) ≤ L) :
    Fintype.card
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne) ≤
      2 * (Fintype.card baseOne * L) *
        (Fintype.card fiberZero + Fintype.card fiberOne) := by sorry
