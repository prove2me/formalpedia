-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_nonempty_dualExposure_of_inside_lt
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.nonempty_dualExposure_of_inside_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:30:57.164759+00:00
-- url     : https://prove2.me/theorems/3345e4ed-4393-4825-bf81-5949aeaf7ece
-- title:
--   LPSTanner Expansion: nonempty dual Exposure of inside lt
-- statement:
--   A supported check block with fewer than 41 supported graph-neighbors has
--   an actual edge on which its local dual word is nonzero and the other endpoint
--   has zero check block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L551-L622
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L551-L622

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.nonempty_dualExposure_of_inside_lt
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q)
    (hg : g ∈ dualSupportVertices q y)
    (hinside : (lpsNeighborsIn401 q hq (dualSupportVertices q y) g).card < 41) :
    Nonempty (DualExposureWitness q hq40 hq y g) := by sorry
