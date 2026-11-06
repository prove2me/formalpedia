-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_eq_trace_entropyFunctionalCalculus
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_trace_entropyFunctionalCalculus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:45:01.376357+00:00
-- url     : https://prove2.me/theorems/0505ae3b-eb99-42de-8ccd-78fb2d9027c9
-- title:
--   Density Operator: von Neumann Entropy eq trace entropy Functional Calculus
-- statement:
--   The entropy is the real trace of Mathlib's finite Hermitian functional calculus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L126-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L126-L141

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

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_trace_entropyFunctionalCalculus
    (rho : DensityOperator H)
    (b : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    (rho.vonNeumannEntropy : Complex) =
      Matrix.trace ((rho.spectralMatrix_isHermitian b).cfc entropyTerm) := by sorry
