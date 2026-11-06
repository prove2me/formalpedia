-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_prod_eq_selected_mul_unselected
-- name    : QEC.Semantics.FiniteInstrument.tensorPower_prod_eq_selected_mul_unselected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:32:36.328383+00:00
-- url     : https://prove2.me/theorems/41750d3e-ec22-48b0-8061-ba31f956a17a
-- title:
--   Finite Instrument: tensor Power prod eq selected mul unselected
-- statement:
--   Every finite product over actual trials splits into its selector-image
--   product and its unselected-trial product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedTrialComplement.lean#L216-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedTrialComplement.lean#L216-L241

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialComplement
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPower_prod_eq_selected_mul_unselected
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (f : Fin attempts → Complex) :
    (∏ trial : Fin attempts, f trial) =
      (∏ slot : Fin required,
        f (tensorPowerAcceptedSelector accepts attempts history required hrequired
          slot)) *
      ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
          hrequired,
        f trial.1 := by sorry
