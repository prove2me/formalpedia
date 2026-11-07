-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_sparseRectangle_lt_le_support_sum
-- name    : QEC.Coding.ProductExpansion.card_sparseRectangle_lt_le_support_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:02.529074+00:00
-- url     : https://prove2.me/theorems/6aed9143-3eae-486c-b78d-b2ac530a8028
-- title:
--   Product Expansion: card sparse Rectangle lt le support sum
-- statement:
--   Exact support-sum upper bound for the number of matrices with fewer than
--   `s` nonzero entries on `A × B`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L97-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L97-L118

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

theorem QEC.Coding.ProductExpansion.card_sparseRectangle_lt_le_support_sum
    [DecidableEq W] (A B : Finset W) (s : Nat) :
    Nat.card {x : Matrix W W F // restrictedWeight x A B < s} ≤
      ∑ S : {S : Finset (W × W) // S ⊆ A ×ˢ B ∧ S.card < s},
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + S.1.card) := by sorry
