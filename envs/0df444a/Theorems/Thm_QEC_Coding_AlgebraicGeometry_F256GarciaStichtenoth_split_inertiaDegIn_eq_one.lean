-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_split_inertiaDegIn_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.split_inertiaDegIn_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:56:54.91629+00:00
-- url     : https://prove2.me/theorems/b7bf4e44-e989-46df-9647-9793444cca42
-- title:
--   F256 Garcia Stichtenoth: split inertia Deg In eq one
-- statement:
--   Every upper prime in this split rational fibre has inertia degree one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SplittingIdeals.lean#L337-L348
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SplittingIdeals.lean#L337-L348

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitIntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplittingIdeals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.split_inertiaDegIn_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).inertiaDegIn
      (SplitIntegralClosure Q P x hx) = 1 := by sorry
