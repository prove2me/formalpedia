-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_restrictedWeight_eq_sum_row_restrictedHammingWeight
-- name    : QEC.Coding.ProductExpansion.restrictedWeight_eq_sum_row_restrictedHammingWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:37:03.547403+00:00
-- url     : https://prove2.me/theorems/e2553e2e-9f46-48d4-85ec-44edc58d075d
-- title:
--   Product Expansion: restricted Weight eq sum row restricted Hamming Weight
-- statement:
--   Count the nonzero entries of a rectangle row by row.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L164-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L164-L168

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.restrictedWeight_eq_sum_row_restrictedHammingWeight
    (x : Matrix W W F) (A B : Finset W) :
    restrictedWeight x A B =
      ∑ i ∈ A, restrictedHammingWeight B (row x i) := by sorry
