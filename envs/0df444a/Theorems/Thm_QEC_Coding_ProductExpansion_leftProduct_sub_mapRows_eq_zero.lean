-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_leftProduct_sub_mapRows_eq_zero
-- name    : QEC.Coding.ProductExpansion.leftProduct_sub_mapRows_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:29:58.621223+00:00
-- url     : https://prove2.me/theorems/ffe67890-5c2d-469f-907c-0312ce207170
-- title:
--   Product Expansion: left Product sub map Rows eq zero
-- statement:
--   Projecting every row onto the first local code kills the other matrix syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L197-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L197-L212

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
omit [DecidableEq F] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.leftProduct_sub_mapRows_eq_zero
    (h : Matrix R W F) (h' : Matrix R' W F)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (T : Word F W →ₗ[F] Word F W)
    (hFix : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier → T c = c) :
    h' * (x - mapRows T x) = 0 := by sorry
