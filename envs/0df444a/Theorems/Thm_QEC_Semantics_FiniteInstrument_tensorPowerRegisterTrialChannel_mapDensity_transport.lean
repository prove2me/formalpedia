-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerRegisterTrialChannel_mapDensity_transport
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerRegisterTrialChannel_mapDensity_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:00:48.296006+00:00
-- url     : https://prove2.me/theorems/c68b18d2-1cf3-475c-a960-c30ac1b7e8b1
-- title:
--   Finite Instrument: tensor Power Register Trial Channel map Density transport
-- statement:
--   Selecting one flattened trial after the standard tensor-power transport
--   is exactly the true recursive coordinate marginal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L388-L415
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L388-L415

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerRegisterTrialChannel_mapDensity_transport
    (iota : Type u) [Fintype iota] [DecidableEq iota]
    (attempts : Nat)
    (rho : DensityOperator
      (tensorPowerCarrier (Qubit.QubitRegister iota) attempts))
    (trial : Fin attempts) :
    (tensorPowerRegisterTrialChannel iota attempts trial).mapDensity
        ((tensorPowerQubitRegisterTransport iota attempts).conjDensity rho) =
      tensorPowerInputMarginal attempts rho trial := by sorry
