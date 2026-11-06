-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_trace_comp_eq_scalar_of_supported_detectableOnWithScalar
-- name    : QEC.Semantics.QuditSubsystem.trace_comp_eq_scalar_of_supported_detectableOnWithScalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:06.467205+00:00
-- url     : https://prove2.me/theorems/67da257e-6290-4e8e-bc57-d2886e46295b
-- title:
--   Qudit Subsystem: trace comp eq scalar of supported detectable On With Scalar
-- statement:
--   The Qudit Subsystem construction uses the trace comp eq scalar of supported detectable On With Scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L832-L860
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L832-L860

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

theorem QEC.Semantics.QuditSubsystem.trace_comp_eq_scalar_of_supported_detectableOnWithScalar
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (C : QuantumCode H) (E : Operator H) (c : Complex)
    (hdetect : DetectableOnWithScalar C E c) (rho : DensityOperator H)
    (hsupported : DensityOperator.SupportedOn C rho) :
    LinearMap.trace Complex H (E.comp rho.toOperator) = c := by sorry
