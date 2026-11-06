-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_artinSchreier_root_order_of_simplePole
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.artinSchreier_root_order_of_simplePole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:11:59.050207+00:00
-- url     : https://prove2.me/theorems/186ee890-5a6a-461a-8650-6694eb1bf174
-- title:
--   Global Place: artin Schreier root order of simple Pole
-- statement:
--   For a quadratic extension, a normalized simple pole downstairs forces
--   both total ramification and a normalized simple pole of the root upstairs.
--   The order-compatibility hypothesis is the ordinary restriction formula for
--   the actual places; no different or pole conclusion is supplied as input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ArtinSchreierOrder.lean#L44-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ArtinSchreierOrder.lean#L44-L74

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.artinSchreier_root_order_of_simplePole [Algebra K L]
    (P : GlobalPlace k K) (Q : GlobalPlace k L) (a : K) (y : L)
    (e : ℕ) (he0 : 0 < e) (he2 : e ≤ 2)
    (hy : y ^ 2 + y = algebraMap K L a)
    (horder : Q.order (algebraMap K L a) = (e : ℤ) * P.order a)
    (ha : P.order a = -1) : e = 2 ∧ Q.order y = -1 := by sorry
