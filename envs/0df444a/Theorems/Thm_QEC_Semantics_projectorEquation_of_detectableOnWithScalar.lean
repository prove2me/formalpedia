-- Prove2me | Theorems.Thm_QEC_Semantics_projectorEquation_of_detectableOnWithScalar
-- name    : QEC.Semantics.projectorEquation_of_detectableOnWithScalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:04:42.206796+00:00
-- url     : https://prove2.me/theorems/bfc74a4c-66e2-44ed-82f5-5831e31b81fc
-- title:
--   Semantics: projector Equation of detectable On With Scalar
-- statement:
--   The Semantics construction uses the projector Equation of detectable On With Scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/Detectability.lean#L30-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/Detectability.lean#L30-L57

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
noncomputable section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.projectorEquation_of_detectableOnWithScalar
    {C : QuantumCode H} {E : Operator H} {c : Complex}
    (h : DetectableOnWithScalar C E c) :
    (C.projector.comp E).comp C.projector = c • C.projector := by sorry
