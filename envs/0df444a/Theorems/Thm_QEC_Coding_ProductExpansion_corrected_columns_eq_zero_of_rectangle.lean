-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_corrected_columns_eq_zero_of_rectangle
-- name    : QEC.Coding.ProductExpansion.corrected_columns_eq_zero_of_rectangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:30:19.558787+00:00
-- url     : https://prove2.me/theorems/a5cee2fd-2df1-4203-bce4-e6dac95e7a98
-- title:
--   Product Expansion: corrected columns eq zero of rectangle
-- statement:
--   After row projection, a zero rectangle and zero left syndrome force the
--   corrected matrix to vanish on every selected column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L254-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L254-L271

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
omit [Fintype R]

theorem QEC.Coding.ProductExpansion.corrected_columns_eq_zero_of_rectangle
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A B : Finset W) (hLarge : Fintype.card W - d < B.card)
    (T : Word F W →ₗ[F] Word F W)
    (hVanish : ∀ y : Word F W, (∀ j ∈ A, y j = 0) → T y = 0)
    (x : Matrix W W F) (hx : ∀ i ∈ B, ∀ j ∈ A, x i j = 0)
    (hLeft : h * (x - mapRows T x) = 0) :
    ∀ j ∈ A, column (x - mapRows T x) j = 0 := by sorry
