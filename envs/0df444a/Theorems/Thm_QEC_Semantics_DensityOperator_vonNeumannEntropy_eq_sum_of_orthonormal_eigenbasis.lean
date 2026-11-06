-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_eq_sum_of_orthonormal_eigenbasis
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_sum_of_orthonormal_eigenbasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:22:45.011611+00:00
-- url     : https://prove2.me/theorems/1ba58d74-3fe5-4f62-b9a7-0314363b793e
-- title:
--   Density Operator: von Neumann Entropy eq sum of orthonormal eigenbasis
-- statement:
--   A finite orthonormal eigenbasis computes the characteristic-polynomial entropy directly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L721-L745
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L721-L745

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

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_sum_of_orthonormal_eigenbasis {ι : Type*}
    [Fintype ι] [DecidableEq ι] (rho : DensityOperator H)
    (b : OrthonormalBasis ι Complex H) (e : ι → Real)
    (happly : ∀ i, rho.toOperator (b i) = (e i : Complex) • b i) :
    rho.vonNeumannEntropy = ∑ i, entropyTerm (e i) := by sorry
