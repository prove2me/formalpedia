-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensorPath_card
-- name    : QEC.Semantics.FiniteInstrument.nestedTensorPath_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:36:50.809268+00:00
-- url     : https://prove2.me/theorems/0bd6abef-67b5-4185-89b7-79a3bf3ddb46
-- title:
--   Finite Instrument: nested Tensor Path card
-- statement:
--   The literal recursive nested path carrier has exactly `branches ^ depth`
--   elements.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/Power.lean#L82-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/Power.lean#L82-L85

import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.nestedTensorPath_card (branches depth : Nat) :
    Fintype.card (nestedTensorPath branches depth) = branches ^ depth := by sorry
