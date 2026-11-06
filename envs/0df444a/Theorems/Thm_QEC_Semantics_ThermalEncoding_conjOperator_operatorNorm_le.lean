-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_conjOperator_operatorNorm_le
-- name    : QEC.Semantics.ThermalEncoding.conjOperator_operatorNorm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:23:10.72366+00:00
-- url     : https://prove2.me/theorems/ce7bc44a-3ef4-47ee-92b8-deab1070425a
-- title:
--   Thermal Encoding: conj Operator operator Norm le
-- statement:
--   Unitary conjugation does not increase the finite operator norm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L183-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L183-L202

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

theorem QEC.Semantics.ThermalEncoding.conjOperator_operatorNorm_le {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K) (A : Operator H) :
    ‖LinearMap.toContinuousLinearMap (U.conjOperator A)‖ ≤
      ‖LinearMap.toContinuousLinearMap A‖ := by sorry
