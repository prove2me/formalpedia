-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_qubitIndex_weightReduced_le
-- name    : QEC.Coding.FiberBundle.card_qubitIndex_weightReduced_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:25:36.263196+00:00
-- url     : https://prove2.me/theorems/0d3302e3-3f55-4c0b-b6ee-89b91949880b
-- title:
--   Fiber Bundle: card qubit Index weight Reduced le
-- statement:
--   The reduced bundle has at most two incidence copies in each of its two
--   middle-chain blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L777-L788
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L777-L788

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

theorem QEC.Coding.FiberBundle.card_qubitIndex_weightReduced_le :
    Fintype.card
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne) ≤
      2 * Fintype.card (ClassicalWeightReduction.Incidence R) *
        (Fintype.card fiberZero + Fintype.card fiberOne) := by sorry
