-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_DensityOperator_spectralEigenvalues_le_one
-- name    : QEC.Semantics.ThermalEncoding.DensityOperator.spectralEigenvalues_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:22:53.394619+00:00
-- url     : https://prove2.me/theorems/0674733a-e6ac-4f31-bec6-ed9e2b378413
-- title:
--   Density Operator: spectral Eigenvalues le one
-- statement:
--   Every spectral weight of a finite density operator is at most one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L32-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L32-L37

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

theorem QEC.Semantics.ThermalEncoding.DensityOperator.spectralEigenvalues_le_one (rho : DensityOperator H)
    (i : Fin (Module.finrank Complex H)) :
    rho.spectralEigenvalues i ≤ 1 := by sorry
