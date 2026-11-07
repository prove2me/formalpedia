-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_mapRows_eq_zero_on_rows_of_vanish_on_rectangle
-- name    : QEC.Coding.ProductExpansion.mapRows_eq_zero_on_rows_of_vanish_on_rectangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:30:02.046101+00:00
-- url     : https://prove2.me/theorems/07df2a8d-ebbc-4033-9faa-5784679758e2
-- title:
--   Product Expansion: map Rows eq zero on rows of vanish on rectangle
-- statement:
--   A row projection depending only on `A` vanishes on rows zero over `A`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L243-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L243-L249

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
omit [Fintype F] [DecidableEq F] [Fintype W] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.mapRows_eq_zero_on_rows_of_vanish_on_rectangle
    (T : Word F W →ₗ[F] Word F W) (A B : Finset W)
    (hVanish : ∀ y : Word F W, (∀ j ∈ A, y j = 0) → T y = 0)
    (x : Matrix W W F) (hx : ∀ i ∈ B, ∀ j ∈ A, x i j = 0) :
    ∀ i ∈ B, mapRows T x i = 0 := by sorry
