-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSelectedRestrictedBasePlace_order_X_sub_one
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRestrictedBasePlace_order_X_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:25:24.366116+00:00
-- url     : https://prove2.me/theorems/f8d71d56-c792-4f84-adbe-fdb7251e8a0c
-- title:
--   F256 Garcia Stichtenoth: source Selected Restricted Base Place order X sub one
-- statement:
--   The restricted place has simple order one at `X-1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedBaseRestriction.lean#L89-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedBaseRestriction.lean#L89-L95

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaceOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncPlaceClassification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedBaseRestriction
set_option autoImplicit false
open Polynomial
open scoped RatFunc WithZero
open MonoidWithZeroHom
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRestrictedBasePlace_order_X_sub_one
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (sourceSelectedRestrictedBasePlace m index).order
        (RatFunc.X - 1) = 1 := by sorry
