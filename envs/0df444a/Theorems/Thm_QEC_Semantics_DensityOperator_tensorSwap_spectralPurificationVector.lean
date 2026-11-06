-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_tensorSwap_spectralPurificationVector
-- name    : QEC.Semantics.DensityOperator.tensorSwap_spectralPurificationVector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:22:09.68441+00:00
-- url     : https://prove2.me/theorems/64fad06a-40af-4923-b3f7-08ed00dba137
-- title:
--   Density Operator: tensor Swap spectral Purification Vector
-- statement:
--   The spectral purification vector is invariant under swapping its equal factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L605-L608
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L605-L608

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.DensityOperator.tensorSwap_spectralPurificationVector (rho : DensityOperator H) :
    tensorSwap H H rho.spectralPurificationVector = rho.spectralPurificationVector := by sorry
