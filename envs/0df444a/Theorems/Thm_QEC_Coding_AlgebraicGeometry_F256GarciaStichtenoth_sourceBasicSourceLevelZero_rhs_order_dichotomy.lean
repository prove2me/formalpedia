-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicSourceLevelZero_rhs_order_dichotomy
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicSourceLevelZero_rhs_order_dichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:22:16.047036+00:00
-- url     : https://prove2.me/theorems/93f89d04-9acf-4ff3-b802-bfbb907fedb1
-- title:
--   F256 Garcia Stichtenoth: source Basic Source Level Zero rhs order dichotomy
-- statement:
--   The basic forward input on the actual level-zero source field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalRecursionOrders.lean#L252-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalRecursionOrders.lean#L252-L256

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicSourceLevelZero_rhs_order_dichotomy
    (P : GlobalPlace F256 (SourceField 0)) :
    P.order (sourceStepRhs (sourceDistinguishedCoordinate 0)) = -1 ∨
      0 ≤ P.order (sourceStepRhs (sourceDistinguishedCoordinate 0)) := by sorry
