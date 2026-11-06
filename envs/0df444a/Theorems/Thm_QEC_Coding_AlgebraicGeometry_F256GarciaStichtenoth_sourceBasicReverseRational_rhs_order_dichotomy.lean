-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicReverseRational_rhs_order_dichotomy
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicReverseRational_rhs_order_dichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:21:29.704824+00:00
-- url     : https://prove2.me/theorems/e2e4d033-25f2-430b-a52d-653ec3a5a363
-- title:
--   F256 Garcia Stichtenoth: source Basic Reverse Rational rhs order dichotomy
-- statement:
--   All lower places of the reverse basic rational projection have the same
--   RHS input on the literal reciprocal successor coordinate.  The recursion's
--   reverse equation identifies this RHS with 1/(x_(i+1)^16+x_(i+1)).
--   No higher-window different formula is inferred here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalRecursionOrders.lean#L344-L354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalRecursionOrders.lean#L344-L354

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicReverseRational_rhs_order_dichotomy
    (i : ℕ)
    (P : GlobalPlace F256 F256⟮(sourceDistinguishedCoordinate (i + 1))⁻¹⟯) :
    P.order (sourceStepRhs
      (AdjoinSimple.gen F256 ((sourceDistinguishedCoordinate (i + 1))⁻¹))) = -1 ∨
      0 ≤ P.order (sourceStepRhs
        (AdjoinSimple.gen F256 ((sourceDistinguishedCoordinate (i + 1))⁻¹))) := by sorry
