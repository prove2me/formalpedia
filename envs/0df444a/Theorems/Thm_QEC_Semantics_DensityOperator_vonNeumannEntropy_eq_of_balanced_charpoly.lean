-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_eq_of_balanced_charpoly
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_of_balanced_charpoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:21:46.116093+00:00
-- url     : https://prove2.me/theorems/ae9aa9f2-d14d-464e-bd59-07190d1389f8
-- title:
--   Density Operator: von Neumann Entropy eq of balanced charpoly
-- statement:
--   Adding any multiplicity of the zero root leaves finite entropy unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L429-L456
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L429-L456

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

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_of_balanced_charpoly {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) (m n : Nat)
    (hcharpoly : (Polynomial.X : Polynomial Complex) ^ m * rho.toOperator.charpoly =
      (Polynomial.X : Polynomial Complex) ^ n * sigma.toOperator.charpoly) :
    rho.vonNeumannEntropy = sigma.vonNeumannEntropy := by sorry
