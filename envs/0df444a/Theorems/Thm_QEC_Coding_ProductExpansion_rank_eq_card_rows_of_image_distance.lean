-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_rank_eq_card_rows_of_image_distance
-- name    : QEC.Coding.ProductExpansion.rank_eq_card_rows_of_image_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:33:56.015225+00:00
-- url     : https://prove2.me/theorems/a705f24a-f308-44a1-a5f3-285d1c55ff02
-- title:
--   Product Expansion: rank eq card rows of image distance
-- statement:
--   Equivalently, a positive-distance generator has maximal row rank.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L911-L925
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L911-L925

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
omit [Fintype F] [Fintype R']

theorem QEC.Coding.ProductExpansion.rank_eq_card_rows_of_image_distance
    (g : Matrix R W F) (d : Nat) (hPositive : 0 < d)
    (hImage : ∀ a : Word F R, a ≠ 0 →
      d ≤ HammingWeight (g.transpose.mulVec a)) :
    g.rank = Fintype.card R := by sorry
