-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperHeightOne_injective
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperHeightOne_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:59:49.469828+00:00
-- url     : https://prove2.me/theorems/11dc6be4-b0ba-4d83-858b-3250a32e3912
-- title:
--   F256 Garcia Stichtenoth: split Upper Height One injective
-- statement:
--   Distinct translations give distinct height-one points.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalSplitting.lean#L51-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalSplitting.lean#L51-L59

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplittingIdeals
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalSplitting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperHeightOne_injective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Function.Injective (splitUpperHeightOne Q P x hx) := by sorry
