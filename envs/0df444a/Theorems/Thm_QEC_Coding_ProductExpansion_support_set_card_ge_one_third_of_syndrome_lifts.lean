-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_support_set_card_ge_one_third_of_syndrome_lifts
-- name    : QEC.Coding.ProductExpansion.support_set_card_ge_one_third_of_syndrome_lifts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:34:24.314222+00:00
-- url     : https://prove2.me/theorems/0dd60d54-a9db-413b-92e2-48463c94ef45
-- title:
--   Product Expansion: support set card ge one third of syndrome lifts
-- statement:
--   The common support of syndrome-spanning lifts has size at least `d/3`.
--   The rank proof applies this to the support union of its minimum-weight
--   representative basis, once those representatives are constructed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1584-L1622
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1584-L1622

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
omit [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.support_set_card_ge_one_third_of_syndrome_lifts
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (S : Finset W)
    (hLifts : ∀ j : W, ∃ y : Word F W,
      (∀ i ∉ S, y i = 0) ∧ h'.mulVec y = h'.mulVec (column x j)) :
    (d : ℝ) / 3 ≤ S.card := by sorry
