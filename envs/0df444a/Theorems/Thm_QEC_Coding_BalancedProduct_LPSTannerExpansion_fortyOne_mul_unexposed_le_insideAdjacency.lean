-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_fortyOne_mul_unexposed_le_insideAdjacency
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.fortyOne_mul_unexposed_le_insideAdjacency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:30:42.97519+00:00
-- url     : https://prove2.me/theorems/3170dc8b-096c-4484-86ce-e37ffe019080
-- title:
--   LPSTanner Expansion: forty One mul unexposed le inside Adjacency
-- statement:
--   The LPSTanner Expansion construction uses the forty One mul unexposed le inside Adjacency property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L668-L697
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L668-L697

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.fortyOne_mul_unexposed_le_insideAdjacency
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q)) :
    41 * (dualUnexposedSupportVertices q hq40 hq y).card ≤
      insideAdjacencyCount401 q hq (dualSupportVertices q y) := by sorry
