-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_operator_eq_sum_rankOne_matrix_basis_reference
-- name    : QEC.Semantics.QuditSubsystem.operator_eq_sum_rankOne_matrix_basis_reference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:17.405707+00:00
-- url     : https://prove2.me/theorems/7378bb36-f224-425e-bccc-fd8cef804b1f
-- title:
--   Qudit Subsystem: operator eq sum rank One matrix basis reference
-- statement:
--   The Qudit Subsystem construction uses the operator eq sum rank One matrix basis reference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L620-L646
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L620-L646

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.operator_eq_sum_rankOne_matrix_basis_reference {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H)
    (A : Operator H) :
    A = ∑ i : κ, ∑ j : κ, inner Complex (b j) (A (b i)) •
      (InnerProductSpace.rankOne Complex (b j) (b i)).toLinearMap := by sorry
