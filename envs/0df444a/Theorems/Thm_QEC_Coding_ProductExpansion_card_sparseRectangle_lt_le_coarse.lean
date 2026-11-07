-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_sparseRectangle_lt_le_coarse
-- name    : QEC.Coding.ProductExpansion.card_sparseRectangle_lt_le_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:54.389502+00:00
-- url     : https://prove2.me/theorems/349be9b5-f472-4063-bc2d-291700a69bb9
-- title:
--   Product Expansion: card sparse Rectangle lt le coarse
-- statement:
--   Coarse PK22 count: rectangle-sparse matrices are bounded by a polynomial
--   support factor times one field-size power for the omitted coordinates and
--   the nonzero rectangle entries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L354-L371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L354-L371

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
omit [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.card_sparseRectangle_lt_le_coarse
    [DecidableEq W] (A B : Finset W) (s m : Nat)
    (hA : Fintype.card W - m ≤ A.card)
    (hB : Fintype.card W - m ≤ B.card) :
    Nat.card {x : Matrix W W F // restrictedWeight x A B < s} ≤
      s * (A.card * B.card + 1) ^ s *
        (Nat.card F) ^ (2 * m * Fintype.card W + s) := by sorry
