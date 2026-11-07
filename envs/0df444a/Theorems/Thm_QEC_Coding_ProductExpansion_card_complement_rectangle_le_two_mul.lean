-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_complement_rectangle_le_two_mul
-- name    : QEC.Coding.ProductExpansion.card_complement_rectangle_le_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:18.463101+00:00
-- url     : https://prove2.me/theorems/7573014d-227c-4335-bbdf-2521a206a79e
-- title:
--   Product Expansion: card complement rectangle le two mul
-- statement:
--   If each side of a square rectangle omits at most `m` coordinates, its
--   complement has at most `2mw` positions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L322-L348
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L322-L348

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
omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.card_complement_rectangle_le_two_mul
    [DecidableEq W] (A B : Finset W) (m : Nat)
    (hA : Fintype.card W - m ≤ A.card)
    (hB : Fintype.card W - m ≤ B.card) :
    (Finset.univ \ (A ×ˢ B) : Finset (W × W)).card ≤
      2 * m * Fintype.card W := by sorry
