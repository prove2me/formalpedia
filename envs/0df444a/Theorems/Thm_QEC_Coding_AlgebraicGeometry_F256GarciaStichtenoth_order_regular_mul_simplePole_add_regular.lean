-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_order_regular_mul_simplePole_add_regular
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.order_regular_mul_simplePole_add_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:05:32.500252+00:00
-- url     : https://prove2.me/theorems/8bdbdbea-f11b-48d7-8c7d-ad3406a38a7f
-- title:
--   F256 Garcia Stichtenoth: order regular mul simple Pole add regular
-- statement:
--   A regular multiple of a normalized simple pole, plus a regular term, is
--   either still a normalized simple pole or becomes regular.  The conclusion
--   uses the discrete integer normalization; it does not assume a cancellation
--   case in advance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreierCancellation.lean#L89-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreierCancellation.lean#L89-L131

import Mathlib.FieldTheory.Perfect
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreierCancellation
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.order_regular_mul_simplePole_add_regular
    (P : GlobalPlace F256 K) (x c r : K)
    (hx : P.order x = -1)
    (hc : GlobalPlace.RegularAt P c)
    (hr : GlobalPlace.RegularAt P r) :
    P.order (c * x + r) = -1 ∨ 0 ≤ P.order (c * x + r) := by sorry
