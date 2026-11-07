-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_check_without_ranked_sparse_exactRectangle_witness
-- name    : QEC.Coding.ProductExpansion.exists_check_without_ranked_sparse_exactRectangle_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:02:54.270759+00:00
-- url     : https://prove2.me/theorems/7a8c60ac-d0a0-43d1-ba91-a0909cdc3568
-- title:
--   Product Expansion: exists check without ranked sparse exact Rectangle witness
-- statement:
--   If the finite union factor is strictly smaller than the rank penalty,
--   there is a check matrix with no ranked sparse witness on any exact large
--   rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1720-L1773
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1720-L1773

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
omit [Fintype R']

theorem QEC.Coding.ProductExpansion.exists_check_without_ranked_sparse_exactRectangle_witness
    [DecidableEq W]
    (h' : Matrix R' W F) (s m k : Nat)
    (hFactor :
      (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s)) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ h : Matrix R W F,
      ¬∃ A B : Finset W,
        A.card = Fintype.card W - m ∧
        B.card = Fintype.card W - m ∧
        ∃ x : Matrix W W F,
          restrictedWeight x A B < s ∧
          k ≤ (h' * x).rank ∧ ProductKernel h h' x := by sorry
