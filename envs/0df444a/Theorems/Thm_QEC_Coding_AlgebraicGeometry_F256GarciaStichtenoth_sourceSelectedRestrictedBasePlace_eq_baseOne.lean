-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSelectedRestrictedBasePlace_eq_baseOne
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRestrictedBasePlace_eq_baseOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:24:52.948651+00:00
-- url     : https://prove2.me/theorems/01cd8efd-d37f-4795-945e-4bf40a7929d5
-- title:
--   F256 Garcia Stichtenoth: source Selected Restricted Base Place eq base One
-- statement:
--   Every selected source valuation restricts to the actual fixed-base
--   rational place `X=1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedBaseRestriction.lean#L107-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedBaseRestriction.lean#L107-L164

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRestrictedBasePlace_eq_baseOne
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSelectedRestrictedBasePlace m index =
      (baseRationalPlace (1 : BasePoint)).place := by sorry
