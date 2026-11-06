-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_prepareRight_apply
-- name    : QEC.Semantics.ThermalEncoding.prepareRight_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:23:44.204849+00:00
-- url     : https://prove2.me/theorems/f9c9cefd-2b24-48e2-87fb-89e0b9540849
-- title:
--   Thermal Encoding: prepare Right apply
-- statement:
--   The preparation channel is exactly right tensoring on operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L849-L884
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L849-L884

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
variable {K : Type}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.ThermalEncoding.prepareRight_apply (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) (A : Operator H) :
    prepareRight H K sigma A = TensorProduct.map A sigma.toOperator := by sorry
