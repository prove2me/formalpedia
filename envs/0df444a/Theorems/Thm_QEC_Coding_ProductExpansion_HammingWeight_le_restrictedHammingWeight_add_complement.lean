-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_le_restrictedHammingWeight_add_complement
-- name    : QEC.Coding.ProductExpansion.HammingWeight_le_restrictedHammingWeight_add_complement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:56.623434+00:00
-- url     : https://prove2.me/theorems/32c7c468-992e-459d-8ef4-8b18a8e22a85
-- title:
--   Product Expansion: Hamming Weight le restricted Hamming Weight add complement
-- statement:
--   A word's total weight is at most its weight on `A` plus the number of
--   coordinates omitted by `A`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L173-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L173-L203

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.HammingWeight_le_restrictedHammingWeight_add_complement
    (A : Finset W) (x : Word F W) :
    HammingWeight x ≤
      restrictedHammingWeight A x + (Fintype.card W - A.card) := by sorry
