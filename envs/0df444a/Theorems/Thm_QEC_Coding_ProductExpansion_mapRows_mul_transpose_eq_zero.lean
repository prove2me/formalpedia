-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_mapRows_mul_transpose_eq_zero
-- name    : QEC.Coding.ProductExpansion.mapRows_mul_transpose_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:55:48.294589+00:00
-- url     : https://prove2.me/theorems/7b9e5547-3e36-4951-9afc-adac32b7d192
-- title:
--   Product Expansion: map Rows mul transpose eq zero
-- statement:
--   A matrix of projected rows is annihilated by the first parity-check matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L216-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L216-L227

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [DecidableEq F] [Fintype R]

theorem QEC.Coding.ProductExpansion.mapRows_mul_transpose_eq_zero
    (h : Matrix R W F) (T : Word F W →ₗ[F] Word F W)
    (hImage : ∀ y : Word F W, T y ∈ (parityCheckCode h).carrier)
    (x : Matrix W W F) :
    mapRows T x * h.transpose = 0 := by sorry
