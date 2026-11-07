-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_sparseRectangle_support_sum_eq_choose_sum
-- name    : QEC.Coding.ProductExpansion.sparseRectangle_support_sum_eq_choose_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:10.742375+00:00
-- url     : https://prove2.me/theorems/f2e57ac4-6202-4cf6-b018-afe583203da3
-- title:
--   Product Expansion: sparse Rectangle support sum eq choose sum
-- statement:
--   Regroup the support sum by the number of nonzero rectangle positions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L155-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L155-L185

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
omit [Field F] [DecidableEq F]

theorem QEC.Coding.ProductExpansion.sparseRectangle_support_sum_eq_choose_sum
    [DecidableEq W] (A B : Finset W) (s : Nat) :
    (∑ S : {S : Finset (W × W) // S ⊆ A ×ˢ B ∧ S.card < s},
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + S.1.card)) =
      ∑ t : Fin s, Nat.choose (A.card * B.card) t.1 *
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + t.1) := by sorry
