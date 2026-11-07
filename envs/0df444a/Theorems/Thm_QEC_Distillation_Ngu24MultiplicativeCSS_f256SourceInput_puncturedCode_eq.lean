-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_puncturedCode_eq
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_puncturedCode_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:15:13.398995+00:00
-- url     : https://prove2.me/theorems/f6208f28-07fe-4f25-a8d6-462a14fb386f
-- title:
--   Ngu24 Multiplicative CSS: f256 Source Input punctured Code eq
-- statement:
--   Puncturing the entire actual code gives the retained-place evaluation code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureInput.lean#L50-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureInput.lean#L50-L55

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_puncturedCode_eq (i : ℕ) :
    (f256SourceInput i).code.carrier.map (f256SourceInput i).puncture =
      (f256PuncturedMultiplicationCode i).carrier := by sorry
