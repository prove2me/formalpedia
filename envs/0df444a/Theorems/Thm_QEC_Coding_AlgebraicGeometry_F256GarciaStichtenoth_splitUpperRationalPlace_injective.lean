-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_injective
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:59:50.856839+00:00
-- url     : https://prove2.me/theorems/8a234ac2-ad1f-423e-9c01-ace75fa17140
-- title:
--   F256 Garcia Stichtenoth: split Upper Rational Place injective
-- statement:
--   The sixteen rational upper places remain pairwise distinct.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalSplitting.lean#L227-L234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalSplitting.lean#L227-L234

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplittingIdeals
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalSplitting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_injective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Function.Injective (splitUpperRationalPlace Q P x hx hregular) := by sorry
