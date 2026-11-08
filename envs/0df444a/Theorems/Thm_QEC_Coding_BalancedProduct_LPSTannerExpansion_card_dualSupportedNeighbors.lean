-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_card_dualSupportedNeighbors
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.card_dualSupportedNeighbors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:30:31.758442+00:00
-- url     : https://prove2.me/theorems/a331b888-2f7a-4414-a6e3-9bdb0d2a7b8a
-- title:
--   LPSTanner Expansion: card dual Supported Neighbors
-- statement:
--   The LPSTanner Expansion construction uses the card dual Supported Neighbors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L525-L534
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L525-L534

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.card_dualSupportedNeighbors
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q) :
    (dualSupportedNeighbors q hq40 hq y g).card =
      HammingWeight
        (wordLinearMapTranspose localParityCheck (checkBlock q g y)) := by sorry
