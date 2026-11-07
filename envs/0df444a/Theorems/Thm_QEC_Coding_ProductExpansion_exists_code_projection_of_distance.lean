-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_code_projection_of_distance
-- name    : QEC.Coding.ProductExpansion.exists_code_projection_of_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:29:37.839845+00:00
-- url     : https://prove2.me/theorems/20cdcf99-0de1-4071-bc49-14db8ac958dd
-- title:
--   Product Expansion: exists code projection of distance
-- statement:
--   A local distance bound supplies the projection used in the nonzero-block proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L157-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L157-L169

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

theorem QEC.Coding.ProductExpansion.exists_code_projection_of_distance
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A : Finset W) (hLarge : Fintype.card W - d < A.card) :
    ∃ T : Word F W →ₗ[F] Word F W,
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier → T c = c) ∧
      (∀ x : Word F W, (∀ i ∈ A, x i = 0) → T x = 0) ∧
      (∀ x : Word F W, T x ∈ (parityCheckCode h).carrier) := by sorry
