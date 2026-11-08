-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_card_dualSupportVertices_le_weight
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.card_dualSupportVertices_le_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:30:42.199674+00:00
-- url     : https://prove2.me/theorems/21fb6817-c092-4284-b54c-5b5eb2655923
-- title:
--   LPSTanner Expansion: card dual Support Vertices le weight
-- statement:
--   The LPSTanner Expansion construction uses the card dual Support Vertices le weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L456-L473
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L456-L473

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.card_dualSupportVertices_le_weight
    (q : ℕ) [Fact q.Prime]
    (y : Word (ZMod 2) (Check401 q)) :
    (dualSupportVertices q y).card ≤ HammingWeight y := by sorry
