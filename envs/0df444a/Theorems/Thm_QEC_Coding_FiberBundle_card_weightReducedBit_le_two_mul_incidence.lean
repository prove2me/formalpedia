-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_weightReducedBit_le_two_mul_incidence
-- name    : QEC.Coding.FiberBundle.card_weightReducedBit_le_two_mul_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:25:46.220333+00:00
-- url     : https://prove2.me/theorems/a9def719-eb8a-4eaa-842f-474d52cf46d1
-- title:
--   Fiber Bundle: card weight Reduced Bit le two mul incidence
-- statement:
--   The Fiber Bundle construction uses the card weight Reduced Bit le two mul incidence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L765-L773
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L765-L773

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

theorem QEC.Coding.FiberBundle.card_weightReducedBit_le_two_mul_incidence :
    Fintype.card (ClassicalWeightReduction.WeightReducedBit R) ≤
      2 * Fintype.card (ClassicalWeightReduction.Incidence R) := by sorry
