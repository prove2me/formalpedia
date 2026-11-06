-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_partialTraceRightRaw_mapDensity_tensorDensity
-- name    : QEC.Semantics.FiniteInstrument.partialTraceRightRaw_mapDensity_tensorDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:41:33.240862+00:00
-- url     : https://prove2.me/theorems/b02e8634-2394-4614-9d07-3952e419964d
-- title:
--   Finite Instrument: partial Trace Right Raw map Density tensor Density
-- statement:
--   Tracing the right factor of a product density returns its left factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L91-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L91-L102

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.partialTraceRightRaw_mapDensity_tensorDensity
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) :
    partialTraceRightRaw_mapDensity H K
        (DensityOperator.tensorDensity rho sigma) = rho := by sorry
