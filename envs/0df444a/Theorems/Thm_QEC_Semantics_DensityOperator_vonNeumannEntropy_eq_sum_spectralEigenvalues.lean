-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_eq_sum_spectralEigenvalues
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_sum_spectralEigenvalues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:08:51.812753+00:00
-- url     : https://prove2.me/theorems/2f2ab48d-2e18-4505-b1d1-c4a5f18e40cb
-- title:
--   Density Operator: von Neumann Entropy eq sum spectral Eigenvalues
-- statement:
--   The characteristic-polynomial definition agrees with the finite eigenvalue sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L71-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L71-L75

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

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_sum_spectralEigenvalues (rho : DensityOperator H) :
    rho.vonNeumannEntropy = ∑ i, entropyTerm (rho.spectralEigenvalues i) := by sorry
