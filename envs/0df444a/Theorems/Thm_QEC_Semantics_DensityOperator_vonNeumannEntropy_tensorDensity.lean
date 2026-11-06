-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_tensorDensity
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_tensorDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:22:56.579025+00:00
-- url     : https://prove2.me/theorems/475da0cd-453a-40f3-b5cc-e105203342f6
-- title:
--   Density Operator: von Neumann Entropy tensor Density
-- statement:
--   Base-two von Neumann entropy is additive for finite tensor density operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L795-L827
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L795-L827

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

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_tensorDensity {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) :
    (tensorDensity rho sigma).vonNeumannEntropy =
      rho.vonNeumannEntropy + sigma.vonNeumannEntropy := by sorry
