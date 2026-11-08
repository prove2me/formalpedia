-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_card_primalSupportVertices_le_twice_weight
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.card_primalSupportVertices_le_twice_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:29:08.234116+00:00
-- url     : https://prove2.me/theorems/f1f58de3-9454-4143-aca8-141a9b0ee97f
-- title:
--   LPSTanner Expansion: card primal Support Vertices le twice weight
-- statement:
--   The LPSTanner Expansion construction uses the card primal Support Vertices le twice weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L228-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L228-L249

import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSTannerExpansion
open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open LPSTanner LPSGraph GVPlus

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.card_primalSupportVertices_le_twice_weight
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    (primalSupportVertices q hq40 hq x).card ≤
      2 * HammingWeight x := by sorry
