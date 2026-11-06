-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerInputMarginal_productInput
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerInputMarginal_productInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:42:14.594667+00:00
-- url     : https://prove2.me/theorems/55529355-cef2-440f-8667-c4d7f44dc18b
-- title:
--   Finite Instrument: tensor Power Input Marginal product Input
-- statement:
--   Every coordinate of a recursively constructed product density has the
--   original one-factor density as its true marginal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L122-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L122-L146

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerInputMarginal_productInput
    {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    forall (attempts : Nat) (trial : Fin attempts),
      tensorPowerInputMarginal attempts
          (tensorPowerProductInput rho rhoUnit attempts) trial = rho := by sorry
