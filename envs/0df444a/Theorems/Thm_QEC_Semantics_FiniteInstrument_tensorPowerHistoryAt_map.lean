-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryAt_map
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerHistoryAt_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:02:10.769509+00:00
-- url     : https://prove2.me/theorems/4fa1f88a-6bfd-45fa-9c59-00d7f938bac1
-- title:
--   Finite Instrument: tensor Power History At map
-- statement:
--   Pointwise history mapping commutes with evaluation at an actual tensor
--   coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProductFunctorial.lean#L91-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProductFunctorial.lean#L91-L109

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped BigOperators TensorProduct
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
  [FiniteQuantumSystem L]

theorem QEC.Semantics.FiniteInstrument.tensorPowerHistoryAt_map
    {beta gamma : Type u} (mapIndex : beta → gamma) :
    ∀ attempts (history : tensorPowerHistory beta attempts)
      (trial : Fin attempts),
      tensorPowerHistoryAt gamma attempts
          (tensorPowerHistoryMap mapIndex attempts history) trial =
        mapIndex (tensorPowerHistoryAt beta attempts history trial) := by sorry
