-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_one_sub_projector_apply_mem_orthogonal
-- name    : QEC.Semantics.QuditSubsystem.one_sub_projector_apply_mem_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:06.967861+00:00
-- url     : https://prove2.me/theorems/cea722d9-7b96-42a1-a9cd-1cabbcdaeef4
-- title:
--   Qudit Subsystem: one sub projector apply mem orthogonal
-- statement:
--   The Qudit Subsystem construction uses the one sub projector apply mem orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L691-L707
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L691-L707

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

theorem QEC.Semantics.QuditSubsystem.one_sub_projector_apply_mem_orthogonal
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (C : QuantumCode H) (z : H) :
    ((1 - C.projector : Operator H) z) ∈ C.carrierᗮ := by sorry
