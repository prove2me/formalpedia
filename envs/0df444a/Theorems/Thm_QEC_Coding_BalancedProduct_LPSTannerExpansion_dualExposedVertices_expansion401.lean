-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_dualExposedVertices_expansion401
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.dualExposedVertices_expansion401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:30:55.753114+00:00
-- url     : https://prove2.me/theorems/9cde3f1b-0262-4157-a18d-887de5cc8745
-- title:
--   LPSTanner Expansion: dual Exposed Vertices expansion401
-- statement:
--   The corrected `10^-7` transpose-radius exposure estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L705-L736
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L705-L736

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.dualExposedVertices_expansion401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq)
    (y : Word (ZMod 2) (Check401 q))
    (hy : 10000000 * HammingWeight y ≤ Fintype.card (Check401 q)) :
    11 * HammingWeight y ≤
      102500 * (dualExposedVertices q hq40 hq y).card := by sorry
