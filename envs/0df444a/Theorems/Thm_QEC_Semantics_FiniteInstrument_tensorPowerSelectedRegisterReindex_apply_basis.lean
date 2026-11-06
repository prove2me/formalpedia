-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedRegisterReindex_apply_basis
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerSelectedRegisterReindex_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:11:42.067985+00:00
-- url     : https://prove2.me/theorems/ba683735-0de1-405c-9b0e-cff3871cb0fb
-- title:
--   Finite Instrument: tensor Power Selected Register Reindex apply basis
-- statement:
--   The selected-register reindexing sends each actual selected-coordinate
--   computational basis vector to its requested selected-slot basis vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystem.lean#L222-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystem.lean#L222-L237

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerSelectedRegisterReindex_apply_basis
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (bits : Qubit.Bitstring
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).SelectedCoordinates) :
    tensorPowerSelectedRegisterReindex accepts attempts history required hrequired ι
      (EuclideanSpace.basisFun (Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).SelectedCoordinates)
        Complex bits) =
      EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
        (tensorPowerSelectedBitstringEquiv accepts attempts history required hrequired ι bits) := by sorry
