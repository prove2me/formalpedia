-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_tensorDensity_eq_double_sum
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_tensorDensity_eq_double_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:22:45.956207+00:00
-- url     : https://prove2.me/theorems/cf8ad385-f280-4de3-8cb8-fc57638427ec
-- title:
--   Density Operator: von Neumann Entropy tensor Density eq double sum
-- statement:
--   The finite tensor density has the pairwise products of the two spectral weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L764-L778
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L764-L778

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

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_tensorDensity_eq_double_sum {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) :
    (tensorDensity rho sigma).vonNeumannEntropy = ∑ i, ∑ j,
      entropyTerm (rho.spectralEigenvalues i * sigma.spectralEigenvalues j) := by sorry
