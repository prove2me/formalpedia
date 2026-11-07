-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_shortenedCode_eq
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_shortenedCode_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:50:27.609338+00:00
-- url     : https://prove2.me/theorems/3f81ba1d-d8c9-47a5-b946-6d3fe561f770
-- title:
--   Ngu24 Multiplicative CSS: f256 Source Input shortened Code eq
-- statement:
--   The constructor's shortened image is the concrete subtracted-divisor AG code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureInput.lean#L37-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureInput.lean#L37-L47

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_shortenedCode_eq (i : ℕ) :
    (f256SourceInput i).shortenedCode = (f256ShortenedMultiplicationCode i).carrier := by sorry
