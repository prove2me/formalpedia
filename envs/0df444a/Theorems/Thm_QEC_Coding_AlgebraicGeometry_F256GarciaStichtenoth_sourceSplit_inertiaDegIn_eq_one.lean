-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplit_inertiaDegIn_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplit_inertiaDegIn_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:29:36.620412+00:00
-- url     : https://prove2.me/theorems/94919383-0e73-49d4-a167-3681626ea8c9
-- title:
--   F256 Garcia Stichtenoth: source Split inertia Deg In eq one
-- statement:
--   Every selected upper prime has inertia degree one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplittingIdeals.lean#L323-L335
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplittingIdeals.lean#L323-L335

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitIntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplittingIdeals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplit_inertiaDegIn_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).inertiaDegIn
      (SourceSplitIntegralClosure Q P x hx) = 1 := by sorry
