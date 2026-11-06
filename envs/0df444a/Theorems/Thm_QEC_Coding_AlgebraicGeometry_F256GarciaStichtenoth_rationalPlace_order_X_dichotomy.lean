-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_rationalPlace_order_X_dichotomy
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalPlace_order_X_dichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:11:03.991206+00:00
-- url     : https://prove2.me/theorems/23875030-bd83-4ecb-b8cb-ef72427b320d
-- title:
--   F256 Garcia Stichtenoth: rational Place order X dichotomy
-- statement:
--   At every normalized place the rational generator is regular or has a
--   simple pole. This also supplies the `w` parameter of the initial additive
--   extension, without selecting only its infinity place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalRecursionOrders.lean#L84-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalRecursionOrders.lean#L84-L90

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalRecursionOrders
set_option autoImplicit false
open IntermediateField
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open scoped BigOperators
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicRationalF256CharTwo
attribute [local instance] sourceBasicRationalF256CharTwo

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalPlace_order_X_dichotomy
    {k : Type*} [_root_.Field k] [Finite k]
    (P : GlobalPlace k (RatFunc k)) :
    P.order RatFunc.X = -1 ∨ 0 ≤ P.order RatFunc.X := by sorry
