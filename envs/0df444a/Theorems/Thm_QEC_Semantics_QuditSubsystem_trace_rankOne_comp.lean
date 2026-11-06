-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_trace_rankOne_comp
-- name    : QEC.Semantics.QuditSubsystem.trace_rankOne_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:14.003834+00:00
-- url     : https://prove2.me/theorems/ffebc2d8-88a5-4fcf-9a65-836762831700
-- title:
--   Qudit Subsystem: trace rank One comp
-- statement:
--   The Qudit Subsystem construction uses the trace rank One comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L876-L889
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L876-L889

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

theorem QEC.Semantics.QuditSubsystem.trace_rankOne_comp
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (E : Operator H) (x y : H) :
    LinearMap.trace Complex H
      ((InnerProductSpace.rankOne Complex x y).toLinearMap.comp E) =
      inner Complex y (E x) := by sorry
