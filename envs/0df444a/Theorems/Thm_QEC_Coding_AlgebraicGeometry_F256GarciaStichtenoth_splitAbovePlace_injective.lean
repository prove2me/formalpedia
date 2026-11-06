-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitAbovePlace_injective
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitAbovePlace_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:59:57.768012+00:00
-- url     : https://prove2.me/theorems/ffae4629-5728-4f07-9e28-015637e4a40d
-- title:
--   F256 Garcia Stichtenoth: split Above Place injective
-- statement:
--   Distinct split height-one points induce distinct normalized global
--   places.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalSplitting.lean#L73-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalSplitting.lean#L73-L89

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplittingIdeals
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalSplitting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitAbovePlace_injective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Function.Injective (splitAbovePlace Q P x hx) := by sorry
