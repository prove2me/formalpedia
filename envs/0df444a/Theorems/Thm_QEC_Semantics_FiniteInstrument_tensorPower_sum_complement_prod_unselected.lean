-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_sum_complement_prod_unselected
-- name    : QEC.Semantics.FiniteInstrument.tensorPower_sum_complement_prod_unselected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:32:14.151359+00:00
-- url     : https://prove2.me/theorems/7a7b55d5-a469-4ad4-a28b-ca86a2350c3b
-- title:
--   Finite Instrument: tensor Power sum complement prod unselected
-- statement:
--   Summing a product of trial-local diagonal factors over the literal
--   complement bitstrings equals the product of the corresponding local sums.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedTrialComplement.lean#L245-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedTrialComplement.lean#L245-L285

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

theorem QEC.Semantics.FiniteInstrument.tensorPower_sum_complement_prod_unselected
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (g : tensorPowerUnselectedTrial accepts attempts history required hrequired →
      Qubit.Bitstring ι → Complex) :
    (∑ complement : Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired
          ι).ComplementCoordinates,
      ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
          hrequired,
        g trial
          (tensorPowerSelectedComplementTrialBitstringEquiv accepts attempts history
            required hrequired ι complement trial)) =
      ∏ trial : tensorPowerUnselectedTrial accepts attempts history required
          hrequired,
        ∑ bits : Qubit.Bitstring ι, g trial bits := by sorry
