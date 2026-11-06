-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_spectralEigenvalues_sum_eq_one
-- name    : QEC.Semantics.DensityOperator.spectralEigenvalues_sum_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:08:39.693835+00:00
-- url     : https://prove2.me/theorems/b6af7a73-41aa-42c1-b769-33a0dfdefb1a
-- title:
--   Density Operator: spectral Eigenvalues sum eq one
-- statement:
--   The Density Operator construction uses the spectral Eigenvalues sum eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L64-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L64-L68

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

theorem QEC.Semantics.DensityOperator.spectralEigenvalues_sum_eq_one (rho : DensityOperator H) :
    (∑ i, rho.spectralEigenvalues i : Real) = 1 := by sorry
