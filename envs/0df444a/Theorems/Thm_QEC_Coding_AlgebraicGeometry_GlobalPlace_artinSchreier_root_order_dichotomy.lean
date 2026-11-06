-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_artinSchreier_root_order_dichotomy
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.artinSchreier_root_order_dichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:12:02.475622+00:00
-- url     : https://prove2.me/theorems/08f1c503-dd57-4104-9104-8a39a8d22922
-- title:
--   Global Place: artin Schreier root order dichotomy
-- statement:
--   The dichotomy used to initialize the source's refined basic edges is
--   preserved by a degree-at-most-two Artin--Schreier step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ArtinSchreierOrder.lean#L87-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ArtinSchreierOrder.lean#L87-L100

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.artinSchreier_root_order_dichotomy [Algebra K L]
    (P : GlobalPlace k K) (Q : GlobalPlace k L) (a : K) (y : L)
    (e : ℕ) (he0 : 0 < e) (he2 : e ≤ 2)
    (hy : y ^ 2 + y = algebraMap K L a)
    (horder : Q.order (algebraMap K L a) = (e : ℤ) * P.order a)
    (ha : P.order a = -1 ∨ 0 ≤ P.order a) :
    Q.order y = -1 ∨ 0 ≤ Q.order y := by sorry
