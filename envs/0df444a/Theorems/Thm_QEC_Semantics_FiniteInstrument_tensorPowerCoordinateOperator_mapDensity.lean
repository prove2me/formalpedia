-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerCoordinateOperator_mapDensity
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerCoordinateOperator_mapDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:42:08.255797+00:00
-- url     : https://prove2.me/theorems/eaa4f3ec-af8a-4882-b735-39785785f6a8
-- title:
--   Finite Instrument: tensor Power Coordinate Operator map Density
-- statement:
--   The recursive coordinate operation returns the definitionally selected
--   true marginal of every density operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L271-L294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L271-L294

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerCoordinateOperator_mapDensity
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] :
    forall (attempts : Nat)
      (rho : DensityOperator (tensorPowerCarrier H attempts))
      (trial : Fin attempts),
      (tensorPowerCoordinateOperator attempts trial).mapDensity rho =
        tensorPowerInputMarginal attempts rho trial := by sorry
