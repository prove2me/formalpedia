-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerAcceptedIndices_card_succ
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerAcceptedIndices_card_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:57:11.232569+00:00
-- url     : https://prove2.me/theorems/c13eae1e-f033-4d42-8bfb-7b8924f10a4c
-- title:
--   Finite Instrument: tensor Power Accepted Indices card succ
-- statement:
--   Accepted-index cardinalities recurse over the actual right-nested finite
--   history.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/FirstMoment.lean#L56-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/FirstMoment.lean#L56-L65

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FirstMoment
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerAcceptedIndices_card_succ {Ω : Type w} [Fintype Ω]
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts : Nat)
    (head : Ω) (tail : tensorPowerHistory Ω attempts) :
    (tensorPowerAcceptedIndices accepts (attempts + 1) (head, tail)).card =
      (if accepts head then 1 else 0) +
        (tensorPowerAcceptedIndices accepts attempts tail).card := by sorry
