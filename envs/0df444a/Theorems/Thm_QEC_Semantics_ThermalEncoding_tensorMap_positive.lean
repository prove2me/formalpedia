-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_tensorMap_positive
-- name    : QEC.Semantics.ThermalEncoding.tensorMap_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:52:22.682496+00:00
-- url     : https://prove2.me/theorems/f755a30d-a129-49c4-812d-c8f58fbcf3c0
-- title:
--   Thermal Encoding: tensor Map positive
-- statement:
--   Tensoring finite positive operators preserves positivity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L83-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L83-L109

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

theorem QEC.Semantics.ThermalEncoding.tensorMap_positive {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator H) (B : Operator K)
    (hA : LinearMap.IsPositive A) (hB : LinearMap.IsPositive B) :
    LinearMap.IsPositive (TensorProduct.map A B) := by sorry
