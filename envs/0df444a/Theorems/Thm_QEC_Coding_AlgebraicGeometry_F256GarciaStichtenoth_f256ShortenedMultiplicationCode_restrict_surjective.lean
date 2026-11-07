-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationCode_restrict_surjective
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationCode_restrict_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:30:00.64916+00:00
-- url     : https://prove2.me/theorems/3b7a7bbc-9869-4609-bf65-589a6cea82a3
-- title:
--   F256 Garcia Stichtenoth: f256 Shortened Multiplication Code restrict surjective
-- statement:
--   Arbitrary field values on a sufficiently small retained region are attained
--   by actual shortened-code words, via Riemann--Roch interpolation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureInterpolation.lean#L33-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureInterpolation.lean#L33-L59

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureInterpolation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationCode_restrict_surjective (i : ℕ)
    (S : Finset (F256MultiplicationRetained i))
    (hS : S.card < (f256GarciaStichtenothLength i + 4) / 5 -
      f256MultiplicationLogicalCount i) :
    Function.Surjective (fun x : (f256ShortenedMultiplicationCode i).carrier =>
      fun j : S => x.val j.val) := by sorry
