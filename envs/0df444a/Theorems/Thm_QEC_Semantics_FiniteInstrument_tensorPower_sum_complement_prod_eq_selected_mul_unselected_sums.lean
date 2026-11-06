-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_sum_complement_prod_eq_selected_mul_unselected_sums
-- name    : QEC.Semantics.FiniteInstrument.tensorPower_sum_complement_prod_eq_selected_mul_unselected_sums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:32:48.014273+00:00
-- url     : https://prove2.me/theorems/d0fa6f0e-fd08-4efb-88dc-ba88f0ef574e
-- title:
--   Finite Instrument: tensor Power sum complement prod eq selected mul unselected sums
-- statement:
--   Summing a trialwise product over one shared complement label factors into
--   the selected trial entries and independent diagonal sums for the unselected
--   trials.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedTrialProduct.lean#L25-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedTrialProduct.lean#L25-L119

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialComplement
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialProduct
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPower_sum_complement_prod_eq_selected_mul_unselected_sums
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (entry : Fin attempts → Qubit.Bitstring ι → Qubit.Bitstring ι → Complex)
    (left right : Qubit.Bitstring (Fin required × ι)) :
    (∑ complement : Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired
          ι).ComplementCoordinates,
      ∏ trial : Fin attempts,
        entry trial
          (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
            ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history
              required hrequired ι).symm (left, complement)) trial)
          (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
            ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts history
              required hrequired ι).symm (right, complement)) trial)) =
      (∏ slot : Fin required,
        entry
          (tensorPowerAcceptedSelector accepts attempts history required hrequired
            slot)
          (fun port => left (slot, port))
          (fun port => right (slot, port))) *
      ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
          hrequired,
        ∑ bits : Qubit.Bitstring ι, entry trial.1 bits bits := by sorry
