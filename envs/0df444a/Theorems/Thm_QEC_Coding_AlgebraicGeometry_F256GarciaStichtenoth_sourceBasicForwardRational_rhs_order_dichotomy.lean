-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicForwardRational_rhs_order_dichotomy
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicForwardRational_rhs_order_dichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:21:23.973831+00:00
-- url     : https://prove2.me/theorems/034be84e-7804-47f2-9a2f-07c16e8e9606
-- title:
--   F256 Garcia Stichtenoth: source Basic Forward Rational rhs order dichotomy
-- statement:
--   All lower places of the forward basic rational projection in the
--   source's Property-(A) pyramid have the simple-pole-or-regular RHS input.
--   This is a statement about F256(x_i), not the whole tower field F_i.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalRecursionOrders.lean#L329-L338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalRecursionOrders.lean#L329-L338

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicForwardRational_rhs_order_dichotomy
    (i : ℕ)
    (P : GlobalPlace F256 F256⟮sourceDistinguishedCoordinate i⟯) :
    P.order (sourceStepRhs
      (AdjoinSimple.gen F256 (sourceDistinguishedCoordinate i))) = -1 ∨
      0 ≤ P.order (sourceStepRhs
        (AdjoinSimple.gen F256 (sourceDistinguishedCoordinate i))) := by sorry
