-- Prove2me | Theorems.Thm_QEC_Semantics_detectableOnWithScalar_of_projectorEquation
-- name    : QEC.Semantics.detectableOnWithScalar_of_projectorEquation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:04:35.363048+00:00
-- url     : https://prove2.me/theorems/e31ea66e-c814-4d40-a257-90f9feeda2e0
-- title:
--   Semantics: detectable On With Scalar of projector Equation
-- statement:
--   The Semantics construction uses the detectable On With Scalar of projector Equation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/Detectability.lean#L59-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/Detectability.lean#L59-L80

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
noncomputable section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.detectableOnWithScalar_of_projectorEquation
    {C : QuantumCode H} {E : Operator H} {c : Complex}
    (h : (C.projector.comp E).comp C.projector = c • C.projector) :
    DetectableOnWithScalar C E c := by sorry
