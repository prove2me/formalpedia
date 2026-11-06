-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_apply_spectralTensorBasis
-- name    : QEC.Semantics.DensityOperator.tensorDensity_apply_spectralTensorBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:22:40.127301+00:00
-- url     : https://prove2.me/theorems/487921aa-3fb1-4a98-9a46-070a569a9c41
-- title:
--   Density Operator: tensor Density apply spectral Tensor Basis
-- statement:
--   The tensor density is diagonal in the tensor product of the two spectral bases.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L748-L761
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L748-L761

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

theorem QEC.Semantics.DensityOperator.tensorDensity_apply_spectralTensorBasis {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K)
    (i : Fin (Module.finrank Complex H)) (j : Fin (Module.finrank Complex K)) :
    (tensorDensity rho sigma).toOperator
        (rho.spectralEigenbasis i ⊗ₜ[Complex] sigma.spectralEigenbasis j) =
      ((rho.spectralEigenvalues i * sigma.spectralEigenvalues j : Real) : Complex) •
        (rho.spectralEigenbasis i ⊗ₜ[Complex] sigma.spectralEigenbasis j) := by sorry
