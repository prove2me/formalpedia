-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_conjDensity
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_conjDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:31:59.303028+00:00
-- url     : https://prove2.me/theorems/ab9e7395-cccd-430f-adf0-49cbac350b36
-- title:
--   Density Operator: von Neumann Entropy conj Density
-- statement:
--   Unitary conjugation preserves the finite-dimensional von Neumann entropy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L144-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L144-L150

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

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_conjDensity {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K) (rho : DensityOperator H) :
    (U.conjDensity rho).vonNeumannEntropy = rho.vonNeumannEntropy := by sorry
