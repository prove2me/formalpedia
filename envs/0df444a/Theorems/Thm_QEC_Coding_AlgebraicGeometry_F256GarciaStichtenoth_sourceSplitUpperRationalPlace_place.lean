-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_place
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_place
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:36:32.159249+00:00
-- url     : https://prove2.me/theorems/563c3a40-91dc-419f-b8ce-2cf10deacf50
-- title:
--   F256 Garcia Stichtenoth: source Split Upper Rational Place place
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Split Upper Rational Place place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRationalSplitting.lean#L231-L239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRationalSplitting.lean#L231-L239

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplittingIdeals
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRationalSplitting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_place
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    (sourceSplitUpperRationalPlace Q P x hx hregular hsplit c).place =
      sourceSplitAbovePlace Q P x hx c := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_place
