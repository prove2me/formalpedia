-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_restrictedWeight_ge_of_many_heavy_rows
-- name    : QEC.Coding.ProductExpansion.restrictedWeight_ge_of_many_heavy_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:37:21.248043+00:00
-- url     : https://prove2.me/theorems/873f8ead-c537-4355-8a09-bbadb1f7821d
-- title:
--   Product Expansion: restricted Weight ge of many heavy rows
-- statement:
--   First branch of the local-star proof: more than `m` rows that are heavy
--   up to a factor two force at least `s` nonzero entries on the large rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L223-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L223-L255

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.restrictedWeight_ge_of_many_heavy_rows
    (f : Matrix W W F) (A B J₂ : Finset W) (d m s : Nat)
    (hJ₂B : J₂ ⊆ B)
    (hA : Fintype.card W - m ≤ A.card)
    (hCount : m < J₂.card)
    (hHeavy : ∀ i ∈ J₂, d ≤ 2 * HammingWeight (row f i))
    (hDistance : 4 * m ≤ d)
    (hScale : 4 * s ≤ m * d) :
    s ≤ restrictedWeight f B A := by sorry
