-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_incidence_eq_sum_bitNeighbor
-- name    : QEC.Coding.FiberBundle.card_incidence_eq_sum_bitNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:20:44.856964+00:00
-- url     : https://prove2.me/theorems/f11d24bd-a456-4224-a741-f019f0ece51c
-- title:
--   Fiber Bundle: card incidence eq sum bit Neighbor
-- statement:
--   The Fiber Bundle construction uses the card incidence eq sum bit Neighbor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L691-L696
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L691-L696

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

theorem QEC.Coding.FiberBundle.card_incidence_eq_sum_bitNeighbor :
    Fintype.card (ClassicalWeightReduction.Incidence R) =
      ∑ b : baseOne,
        Fintype.card (ClassicalWeightReduction.BitNeighbor R b) := by sorry
