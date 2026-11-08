-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_weight_le_200_mul_card_dualSupportVertices
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.weight_le_200_mul_card_dualSupportVertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:30:38.983207+00:00
-- url     : https://prove2.me/theorems/4f7d513e-0ec1-432d-910d-74248494391d
-- title:
--   LPSTanner Expansion: weight le 200 mul card dual Support Vertices
-- statement:
--   The LPSTanner Expansion construction uses the weight le 200 mul card dual Support Vertices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L475-L498
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L475-L498

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.weight_le_200_mul_card_dualSupportVertices
    (q : ℕ) [Fact q.Prime]
    (y : Word (ZMod 2) (Check401 q)) :
    HammingWeight y ≤ 200 * (dualSupportVertices q y).card := by sorry
