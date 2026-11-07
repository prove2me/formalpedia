-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_shortened_dimension
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_shortened_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:13:34.086545+00:00
-- url     : https://prove2.me/theorems/2ae6c841-ae67-40e3-9546-3f16e872787d
-- title:
--   Ngu24 Multiplicative CSS: f256 Source Input shortened dimension
-- statement:
--   The Ngu24 Multiplicative CSS construction uses the f256 Source Input shortened dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureInput.lean#L57-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureInput.lean#L57-L61

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_shortened_dimension (i : ℕ) :
    Module.finrank F256 (f256SourceInput i).shortenedCode + f256MultiplicationLogicalCount i =
      Dimension (f256MultiplicationCode i) := by sorry
