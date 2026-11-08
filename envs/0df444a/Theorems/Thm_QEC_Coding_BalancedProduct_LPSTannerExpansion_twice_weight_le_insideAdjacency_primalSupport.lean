-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_twice_weight_le_insideAdjacency_primalSupport
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.twice_weight_le_insideAdjacency_primalSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:29:44.271626+00:00
-- url     : https://prove2.me/theorems/d72d614e-0d05-4d33-8e97-222231b74fd0
-- title:
--   LPSTanner Expansion: twice weight le inside Adjacency primal Support
-- statement:
--   Every supported edge contributes both oriented incidences inside the set
--   of vertices incident to the edge support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L253-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L253-L299

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.twice_weight_le_insideAdjacency_primalSupport
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    2 * HammingWeight x ≤
      insideAdjacencyCount401 q hq
        (primalSupportVertices q hq40 hq x) := by sorry
