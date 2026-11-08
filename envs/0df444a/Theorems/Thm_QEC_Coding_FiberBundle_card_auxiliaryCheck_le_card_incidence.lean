-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_auxiliaryCheck_le_card_incidence
-- name    : QEC.Coding.FiberBundle.card_auxiliaryCheck_le_card_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:25:18.614848+00:00
-- url     : https://prove2.me/theorems/98ea980d-2ea6-4e53-9529-fe2e52c2eb14
-- title:
--   Fiber Bundle: card auxiliary Check le card incidence
-- statement:
--   The Fiber Bundle construction uses the card auxiliary Check le card incidence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L714-L722
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L714-L722

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

theorem QEC.Coding.FiberBundle.card_auxiliaryCheck_le_card_incidence :
    Fintype.card (ClassicalWeightReduction.AuxiliaryCheck R) ≤
      Fintype.card (ClassicalWeightReduction.Incidence R) := by sorry
