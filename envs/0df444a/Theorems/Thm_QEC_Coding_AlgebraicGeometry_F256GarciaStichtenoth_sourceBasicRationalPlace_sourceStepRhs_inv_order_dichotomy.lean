-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicRationalPlace_sourceStepRhs_inv_order_dichotomy
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicRationalPlace_sourceStepRhs_inv_order_dichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:19:53.338444+00:00
-- url     : https://prove2.me/theorems/87187de1-9349-41a8-8356-bea700769801
-- title:
--   F256 Garcia Stichtenoth: source Basic Rational Place source Step Rhs inv order dichotomy
-- statement:
--   The same basic input for the reciprocal rational coordinate, as used by
--   the reverse source equation.  Pullback retains the arbitrary supplied place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalRecursionOrders.lean#L260-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalRecursionOrders.lean#L260-L270

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicRationalPlace_sourceStepRhs_inv_order_dichotomy
    (P : GlobalPlace F256 (RatFunc F256)) :
    P.order (sourceStepRhs (RatFunc.X⁻¹)) = -1 ∨
      0 ≤ P.order (sourceStepRhs (RatFunc.X⁻¹)) := by sorry
