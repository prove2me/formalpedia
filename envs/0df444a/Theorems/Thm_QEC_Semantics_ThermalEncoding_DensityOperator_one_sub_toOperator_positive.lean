-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_DensityOperator_one_sub_toOperator_positive
-- name    : QEC.Semantics.ThermalEncoding.DensityOperator.one_sub_toOperator_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:22:58.015892+00:00
-- url     : https://prove2.me/theorems/2c79c44b-ff00-4d1b-a68e-c9e1e8b1db0d
-- title:
--   Density Operator: one sub to Operator positive
-- statement:
--   A density operator lies below the identity in the positive-operator order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L40-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L40-L78

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
open QEC.Semantics.ThermalEncoding.DensityOperator

theorem QEC.Semantics.ThermalEncoding.DensityOperator.one_sub_toOperator_positive (rho : DensityOperator H) :
    LinearMap.IsPositive (1 - rho.toOperator) := by sorry
