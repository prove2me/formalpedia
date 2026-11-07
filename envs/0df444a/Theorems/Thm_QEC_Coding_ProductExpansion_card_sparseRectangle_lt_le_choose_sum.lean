-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_sparseRectangle_lt_le_choose_sum
-- name    : QEC.Coding.ProductExpansion.card_sparseRectangle_lt_le_choose_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:34:56.630391+00:00
-- url     : https://prove2.me/theorems/f0776e31-806a-47c6-9e10-737ee4a6d9a1
-- title:
--   Product Expansion: card sparse Rectangle lt le choose sum
-- statement:
--   The paper's finite support count, before replacing binomial coefficients
--   by a coarser elementary upper bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L189-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L189-L196

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

theorem QEC.Coding.ProductExpansion.card_sparseRectangle_lt_le_choose_sum
    [DecidableEq W] (A B : Finset W) (s : Nat) :
    Nat.card {x : Matrix W W F // restrictedWeight x A B < s} ≤
      ∑ t : Fin s, Nat.choose (A.card * B.card) t.1 *
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + t.1) := by sorry
