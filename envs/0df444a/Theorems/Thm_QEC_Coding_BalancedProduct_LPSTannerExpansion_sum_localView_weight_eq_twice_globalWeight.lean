-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_sum_localView_weight_eq_twice_globalWeight
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.sum_localView_weight_eq_twice_globalWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:29:23.231515+00:00
-- url     : https://prove2.me/theorems/3bc4ee8a-3075-4cc6-93be-67424025b981
-- title:
--   LPSTanner Expansion: sum local View weight eq twice global Weight
-- statement:
--   Exact handshake identity for the support of an edge word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L161-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L161-L170

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.sum_localView_weight_eq_twice_globalWeight
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    (∑ g, HammingWeight (localView q hq40 hq g x)) =
      2 * HammingWeight x := by sorry
