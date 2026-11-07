-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_restriction_injective_of_distance
-- name    : QEC.Coding.ProductExpansion.restriction_injective_of_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:29:26.335731+00:00
-- url     : https://prove2.me/theorems/3836dfbf-f1e5-45fd-8c9f-f67ca513ef36
-- title:
--   Product Expansion: restriction injective of distance
-- statement:
--   Restriction to a sufficiently large coordinate set determines every codeword.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L96-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L96-L113

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

theorem QEC.Coding.ProductExpansion.restriction_injective_of_distance
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A : Finset W) (hLarge : Fintype.card W - d < A.card) :
    Function.Injective (fun c : (parityCheckCode h).carrier =>
      fun i : {i : W // i ∈ A} => c.1 i.1) := by sorry
