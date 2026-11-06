-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_trace_comp_rankOne
-- name    : QEC.Semantics.QuditSubsystem.trace_comp_rankOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:43:14.601734+00:00
-- url     : https://prove2.me/theorems/4b24e4f4-272d-44a9-8932-16308d5e5e33
-- title:
--   Qudit Subsystem: trace comp rank One
-- statement:
--   The Qudit Subsystem construction uses the trace comp rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L863-L873
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L863-L873

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

theorem QEC.Semantics.QuditSubsystem.trace_comp_rankOne
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (Z : Operator H) (v u : H) :
    LinearMap.trace Complex H
      (Z.comp (InnerProductSpace.rankOne Complex v u).toLinearMap) =
      inner Complex u (Z v) := by sorry
