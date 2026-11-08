-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_fortyOne_mul_heavy_le_twice_weight
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.fortyOne_mul_heavy_le_twice_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:29:38.887463+00:00
-- url     : https://prove2.me/theorems/50986d2a-9f01-4625-bddc-7ef4b6edd7df
-- title:
--   LPSTanner Expansion: forty One mul heavy le twice weight
-- statement:
--   The LPSTanner Expansion construction uses the forty One mul heavy le twice weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L349-L368
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L349-L368

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.fortyOne_mul_heavy_le_twice_weight
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    41 * (primalHeavyVertices q hq40 hq x).card ≤
      2 * HammingWeight x := by sorry
