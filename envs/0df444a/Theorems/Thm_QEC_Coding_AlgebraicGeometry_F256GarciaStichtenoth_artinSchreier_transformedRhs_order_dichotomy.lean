-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_artinSchreier_transformedRhs_order_dichotomy
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.artinSchreier_transformedRhs_order_dichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:05:41.747917+00:00
-- url     : https://prove2.me/theorems/41940897-a917-4000-b171-88148a0b9776
-- title:
--   F256 Garcia Stichtenoth: artin Schreier transformed Rhs order dichotomy
-- statement:
--   The transformed Artin--Schreier right-hand side has the local dichotomy
--   needed by the compositum proof once the coefficient and error term have been
--   shown regular at the upper place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreierCancellation.lean#L136-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreierCancellation.lean#L136-L152

import Mathlib.FieldTheory.Perfect
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreierCancellation
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.artinSchreier_transformedRhs_order_dichotomy
    (P : GlobalPlace F256 K) (x z₁ u w : K)
    (hx : P.order x = -1)
    (hu : GlobalPlace.RegularAt P u)
    (hzw : GlobalPlace.RegularAt P (z₁ * w)) :
    P.order ((u - u ^ 2) * x + z₁ * w) = -1 ∨
      0 ≤ P.order ((u - u ^ 2) * x + z₁ * w) := by sorry
