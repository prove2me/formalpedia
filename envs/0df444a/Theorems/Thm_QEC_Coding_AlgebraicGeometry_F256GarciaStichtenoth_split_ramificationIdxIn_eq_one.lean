-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_split_ramificationIdxIn_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.split_ramificationIdxIn_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:56:43.154085+00:00
-- url     : https://prove2.me/theorems/566b40f7-9175-4851-a33e-e30b3b61c2dc
-- title:
--   F256 Garcia Stichtenoth: split ramification Idx In eq one
-- statement:
--   Every upper prime in this split rational fibre has ramification index
--   one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SplittingIdeals.lean#L324-L334
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SplittingIdeals.lean#L324-L334

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitIntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplittingIdeals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.split_ramificationIdxIn_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).ramificationIdxIn
      (SplitIntegralClosure Q P x hx) = 1 := by sorry
