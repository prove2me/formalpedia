-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSelectedRationalPlace_order_galoisBaseParameter_sub_one
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRationalPlace_order_galoisBaseParameter_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:48:34.318857+00:00
-- url     : https://prove2.me/theorems/1634c0d2-6f89-4308-b355-5868066bb995
-- title:
--   F256 Garcia Stichtenoth: source Selected Rational Place order galois Base Parameter sub one
-- statement:
--   At every explicitly selected source place, `z-1` is a local uniformizer:
--   its normalized order is exactly one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaceOrder.lean#L110-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaceOrder.lean#L110-L143

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaceOrder
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRationalPlace_order_galoisBaseParameter_sub_one :
    ∀ (m : ℕ) (index : SourceSelectedPlaceIndex m),
      (sourceSelectedRationalPlace m index).place.order
          (sourceGaloisBaseParameter m - 1) = 1
  := by sorry
