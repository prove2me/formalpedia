-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_kernel_restrict_surjective
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_kernel_restrict_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:18:37.058979+00:00
-- url     : https://prove2.me/theorems/6324aae8-af74-401c-9fcb-edabec51a0ea
-- title:
--   Ngu24 Multiplicative CSS: f256 Source Input kernel restrict surjective
-- statement:
--   The concrete shortened kernel can prescribe arbitrary values in a small region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureDistance.lean#L26-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureDistance.lean#L26-L41

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureInterpolation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CosetDetectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Semantics
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_kernel_restrict_surjective (i : ℕ)
    (S : Finset (f256SourceInput i).PivotComplement)
    (hS : S.card < (f256GarciaStichtenothLength i + 4) / 5 -
      f256MultiplicationLogicalCount i) :
    Function.Surjective (fun h : (f256SourceInput i).H0 =>
      fun j : S => (f256SourceInput i).puncture h.val.val j.val) := by sorry
