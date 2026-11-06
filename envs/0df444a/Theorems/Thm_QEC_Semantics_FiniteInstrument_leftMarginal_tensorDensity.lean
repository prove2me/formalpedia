-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_leftMarginal_tensorDensity
-- name    : QEC.Semantics.FiniteInstrument.leftMarginal_tensorDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:41:40.487201+00:00
-- url     : https://prove2.me/theorems/4b6eb611-bce9-4280-8247-4ef770663f67
-- title:
--   Finite Instrument: left Marginal tensor Density
-- statement:
--   Tracing the left factor of a product density returns its right factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L106-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L106-L117

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.leftMarginal_tensorDensity
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) :
    DensityOperator.leftMarginal
        (DensityOperator.tensorDensity rho sigma) = sigma := by sorry
