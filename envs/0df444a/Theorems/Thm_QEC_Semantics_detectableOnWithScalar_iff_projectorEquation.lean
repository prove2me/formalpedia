-- Prove2me | Theorems.Thm_QEC_Semantics_detectableOnWithScalar_iff_projectorEquation
-- name    : QEC.Semantics.detectableOnWithScalar_iff_projectorEquation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:15:26.007996+00:00
-- url     : https://prove2.me/theorems/8f53b901-aed6-43ad-8575-d6506d649625
-- title:
--   Semantics: detectable On With Scalar iff projector Equation
-- statement:
--   Fixed-scalar matrix-element detectability is exactly projector compression.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/Detectability.lean#L83-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/Detectability.lean#L83-L89

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
noncomputable section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.detectableOnWithScalar_iff_projectorEquation
    (C : QuantumCode H) (E : Operator H) (c : Complex) :
    DetectableOnWithScalar C E c ↔
      (C.projector.comp E).comp C.projector = c • C.projector := by sorry
