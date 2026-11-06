-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplit_ramificationIdxIn_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplit_ramificationIdxIn_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:29:58.020452+00:00
-- url     : https://prove2.me/theorems/f91c6a10-7a92-4fcf-a4fd-c73d935248f4
-- title:
--   F256 Garcia Stichtenoth: source Split ramification Idx In eq one
-- statement:
--   Every selected upper prime has ramification index one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplittingIdeals.lean#L309-L320
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplittingIdeals.lean#L309-L320

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitIntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplittingIdeals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplit_ramificationIdxIn_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).ramificationIdxIn
      (SourceSplitIntegralClosure Q P x hx) = 1 := by sorry
