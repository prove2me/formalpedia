-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_artinSchreier_root_order_nonnegative
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.artinSchreier_root_order_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:11:57.234515+00:00
-- url     : https://prove2.me/theorems/20432044-8094-4984-ba23-d7936f5ca208
-- title:
--   Global Place: artin Schreier root order nonnegative
-- statement:
--   Regular right-hand sides have regular roots at every upper place.
--   This applies to each stage, not merely to a selected extension of a place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ArtinSchreierOrder.lean#L78-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ArtinSchreierOrder.lean#L78-L83

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.artinSchreier_root_order_nonnegative (Q : GlobalPlace k L)
    (y : L) (ha : 0 ≤ Q.order (y ^ 2 + y)) : 0 ≤ Q.order y := by sorry
