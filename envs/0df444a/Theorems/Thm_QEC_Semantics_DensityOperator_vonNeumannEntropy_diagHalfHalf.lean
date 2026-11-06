-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_diagHalfHalf
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_diagHalfHalf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:45:16.11702+00:00
-- url     : https://prove2.me/theorems/00cdf621-ee1a-4afd-84b6-1beee40e2ac4
-- title:
--   Density Operator: von Neumann Entropy diag Half Half
-- statement:
--   The Density Operator construction uses the von Neumann Entropy diag Half Half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L220-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L220-L225

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

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_diagHalfHalf : diagHalfHalf.vonNeumannEntropy = 1 := by sorry
