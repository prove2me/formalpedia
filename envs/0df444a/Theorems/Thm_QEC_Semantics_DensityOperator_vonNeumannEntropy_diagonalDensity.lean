-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_diagonalDensity
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_diagonalDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:20:45.475209+00:00
-- url     : https://prove2.me/theorems/8cd91b74-3662-4710-bfef-edf419e45c9e
-- title:
--   Density Operator: von Neumann Entropy diagonal Density
-- statement:
--   The entropy of a diagonal density operator is the corresponding finite weight sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L193-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L193-L201

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_diagonalDensity (n : Nat) (p : Fin n -> Real)
    (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    (diagonalDensity n p hp hsum).vonNeumannEntropy = ∑ i, entropyTerm (p i) := by sorry
