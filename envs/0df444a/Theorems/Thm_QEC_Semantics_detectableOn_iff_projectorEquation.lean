-- Prove2me | Theorems.Thm_QEC_Semantics_detectableOn_iff_projectorEquation
-- name    : QEC.Semantics.detectableOn_iff_projectorEquation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:33:40.853979+00:00
-- url     : https://prove2.me/theorems/cd3bc8e3-74cc-4177-9637-0444b5b7eb7c
-- title:
--   Semantics: detectable On iff projector Equation
-- statement:
--   Semantic detectability is equivalent to a scalar projector-compression equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/Detectability.lean#L92-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/Detectability.lean#L92-L100

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
noncomputable section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.detectableOn_iff_projectorEquation
    (C : QuantumCode H) (E : Operator H) :
    DetectableOn C E ↔
      ∃ c : Complex, (C.projector.comp E).comp C.projector = c • C.projector := by sorry
