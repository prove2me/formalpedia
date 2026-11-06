-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_fixedDensityReplacementChannel_apply_rankOne
-- name    : QEC.Semantics.FiniteInstrument.fixedDensityReplacementChannel_apply_rankOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:55:04.474219+00:00
-- url     : https://prove2.me/theorems/7ef629e7-2c53-45c5-b4d0-a6c6e1c83a02
-- title:
--   Finite Instrument: fixed Density Replacement Channel apply rank One
-- statement:
--   On a rank-one input, the physical replacement channel retains only the
--   input trace coefficient and prepares the supplied density operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L58-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L58-L77

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel
set_option autoImplicit false
universe v w
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.fixedDensityReplacementChannel_apply_rankOne (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) (h g : H) :
    fixedDensityReplacementChannel H K sigma
      (InnerProductSpace.rankOne Complex h g).toLinearMap =
        (inner Complex g h) • sigma.toOperator := by sorry
