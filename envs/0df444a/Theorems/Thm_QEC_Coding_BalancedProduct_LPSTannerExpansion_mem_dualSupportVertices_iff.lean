-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_mem_dualSupportVertices_iff
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.mem_dualSupportVertices_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:29:16.613668+00:00
-- url     : https://prove2.me/theorems/69924e13-33c6-491e-b02f-1ad11d4831e3
-- title:
--   LPSTanner Expansion: mem dual Support Vertices iff
-- statement:
--   The LPSTanner Expansion construction uses the mem dual Support Vertices iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L449-L454
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L449-L454

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.mem_dualSupportVertices_iff
    (q : ℕ) [Fact q.Prime]
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q) :
    g ∈ dualSupportVertices q y ↔ checkBlock q g y ≠ 0 := by sorry
