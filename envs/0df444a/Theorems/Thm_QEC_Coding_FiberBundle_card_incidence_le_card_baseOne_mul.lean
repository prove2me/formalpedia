-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_incidence_le_card_baseOne_mul
-- name    : QEC.Coding.FiberBundle.card_incidence_le_card_baseOne_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:25:12.61354+00:00
-- url     : https://prove2.me/theorems/251637f1-0f04-4b56-b02c-55e12351cd91
-- title:
--   Fiber Bundle: card incidence le card base One mul
-- statement:
--   The Fiber Bundle construction uses the card incidence le card base One mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L698-L712
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L698-L712

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

theorem QEC.Coding.FiberBundle.card_incidence_le_card_baseOne_mul
    {L : Nat}
    (hBitDegree : ∀ b : baseOne,
      Fintype.card (ClassicalWeightReduction.BitNeighbor R b) ≤ L) :
    Fintype.card (ClassicalWeightReduction.Incidence R) ≤
      Fintype.card baseOne * L := by sorry
