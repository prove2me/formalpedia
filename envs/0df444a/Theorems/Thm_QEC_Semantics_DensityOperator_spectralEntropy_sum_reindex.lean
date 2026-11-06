-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_spectralEntropy_sum_reindex
-- name    : QEC.Semantics.DensityOperator.spectralEntropy_sum_reindex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:44:41.636985+00:00
-- url     : https://prove2.me/theorems/a547d461-fd31-4847-bdf3-9e6e75b1dec2
-- title:
--   Density Operator: spectral Entropy sum reindex
-- statement:
--   Reindexing a finite spectral enumeration does not change the entropy sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L78-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L78-L82

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

theorem QEC.Semantics.DensityOperator.spectralEntropy_sum_reindex {ι : Type*} [Fintype ι]
    (rho : DensityOperator H) (e : ι ≃ Fin (Module.finrank Complex H)) :
    (∑ i, entropyTerm (rho.spectralEigenvalues (e i))) = rho.vonNeumannEntropy := by sorry
