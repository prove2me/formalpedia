-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_distance_le_four_mul_restrictedHammingWeight
-- name    : QEC.Coding.ProductExpansion.distance_le_four_mul_restrictedHammingWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:37:12.832345+00:00
-- url     : https://prove2.me/theorems/7d4d18a3-bac1-412d-a8b9-114f88f79b2b
-- title:
--   Product Expansion: distance le four mul restricted Hamming Weight
-- statement:
--   A globally heavy row remains quarter-heavy on a set omitting at most `m`
--   coordinates when `d ≥ 4m`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L208-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L208-L218

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.distance_le_four_mul_restrictedHammingWeight
    (A : Finset W) (x : Word F W) (d m : Nat)
    (hA : Fintype.card W - m ≤ A.card)
    (hHeavy : d ≤ 2 * HammingWeight x)
    (hDistance : 4 * m ≤ d) :
    d ≤ 4 * restrictedHammingWeight A x := by sorry
