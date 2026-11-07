-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_productExpanding_of_no_ranked_sparse_exactRectangle_witness
-- name    : QEC.Coding.ProductExpansion.productExpanding_of_no_ranked_sparse_exactRectangle_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:34:23.437994+00:00
-- url     : https://prove2.me/theorems/55ce2d4c-ffc6-4262-a422-f8ed85bf9d58
-- title:
--   Product Expansion: product Expanding of no ranked sparse exact Rectangle witness
-- statement:
--   Absence of ranked sparse exact-rectangle witnesses, together with the
--   classical distance hypotheses used by the local rank lemma, gives the actual
--   PK22 product-expansion predicate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1779-L1810
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1779-L1810

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R]

theorem QEC.Coding.ProductExpansion.productExpanding_of_no_ranked_sparse_exactRectangle_witness
    (h : Matrix R W F) (h' : Matrix R' W F) (d m s k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hNoBad : ¬∃ A B : Finset W,
      A.card = Fintype.card W - m ∧
      B.card = Fintype.card W - m ∧
      ∃ x : Matrix W W F,
        restrictedWeight x A B < s ∧
        k ≤ (h' * x).rank ∧ ProductKernel h h' x) :
    ProductExpanding h h' s m
      ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by sorry
