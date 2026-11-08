-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_activeLightVertices_expansion401
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.activeLightVertices_expansion401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:29:37.818548+00:00
-- url     : https://prove2.me/theorems/927ee0aa-a908-4dc0-8147-8f8a95f5be7b
-- title:
--   LPSTanner Expansion: active Light Vertices expansion401
-- statement:
--   The corrected `10^-7` primal-radius support estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L371-L405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L371-L405

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.activeLightVertices_expansion401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq)
    (x : Word (ZMod 2) (Edge401 q hq))
    (hx : 10000000 * HammingWeight x ≤
      Fintype.card (Edge401 q hq)) :
    44 * HammingWeight x ≤
      41123 * (activeLightVertices q hq40 hq x).card := by sorry
