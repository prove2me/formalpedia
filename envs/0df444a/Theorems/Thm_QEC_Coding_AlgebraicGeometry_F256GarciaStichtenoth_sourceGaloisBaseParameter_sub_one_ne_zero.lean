-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisBaseParameter_sub_one_ne_zero
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisBaseParameter_sub_one_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:48:26.131845+00:00
-- url     : https://prove2.me/theorems/f20e829b-a353-4c8b-9c60-e3c126239f6f
-- title:
--   F256 Garcia Stichtenoth: source Galois Base Parameter sub one ne zero
-- statement:
--   The fixed-base function `z-1` remains nonzero in every source level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaceOrder.lean#L96-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaceOrder.lean#L96-L101

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaceOrder
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisBaseParameter_sub_one_ne_zero (m : ℕ) :
    sourceGaloisBaseParameter m - 1 ≠ 0 := by sorry
