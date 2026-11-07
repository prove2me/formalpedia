-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_mapRows_left_mul
-- name    : QEC.Coding.ProductExpansion.mapRows_left_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:29:55.108935+00:00
-- url     : https://prove2.me/theorems/42384820-e2a9-468d-942e-5caf945a3513
-- title:
--   Product Expansion: map Rows left mul
-- statement:
--   A rowwise linear operation commutes with left matrix multiplication.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L184-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L184-L193

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
omit [Fintype F] [DecidableEq F] [Fintype W]

theorem QEC.Coding.ProductExpansion.mapRows_left_mul
    {I J : Type v} [Fintype I]
    (T : Word F W →ₗ[F] Word F W)
    (H : Matrix J I F) (x : Matrix I W F) :
    mapRows T (H * x) = H * mapRows T x := by sorry
