-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_tensorDensityLeft_operatorNorm_le_one
-- name    : QEC.Semantics.ThermalEncoding.tensorDensityLeft_operatorNorm_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:23:11.802416+00:00
-- url     : https://prove2.me/theorems/76fcd4f6-6c45-4371-9258-b52fdaf5d20a
-- title:
--   Thermal Encoding: tensor Density Left operator Norm le one
-- statement:
--   A density operator tensored with an identity remains a contraction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L156-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L156-L180

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.ThermalEncoding.tensorDensityLeft_operatorNorm_le_one {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) :
    ‖LinearMap.toContinuousLinearMap
      (TensorProduct.map rho.toOperator (1 : Operator K))‖ ≤ 1 := by sorry
