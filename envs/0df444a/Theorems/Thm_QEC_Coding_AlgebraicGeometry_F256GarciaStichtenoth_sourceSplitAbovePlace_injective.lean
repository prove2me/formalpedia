-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitAbovePlace_injective
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitAbovePlace_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:33:35.419956+00:00
-- url     : https://prove2.me/theorems/8e0af0ba-366c-420d-8f63-cc36c60b92a1
-- title:
--   F256 Garcia Stichtenoth: source Split Above Place injective
-- statement:
--   Distinct selected source height-one points induce distinct normalized
--   global places.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRationalSplitting.lean#L73-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRationalSplitting.lean#L73-L90

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplittingIdeals
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRationalSplitting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitAbovePlace_injective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    Function.Injective (sourceSplitAbovePlace Q P x hx) := by sorry
