-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_be20Tanner_coboundary_expansion
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.be20Tanner_coboundary_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:31:05.111374+00:00
-- url     : https://prove2.me/theorems/9986098e-4dae-4c3c-9c64-87167d86821c
-- title:
--   LPSTanner Expansion: be20 Tanner coboundary expansion
-- statement:
--   Concrete transpose BE20 Tanner expansion at the owner-approved repaired
--   radius `10^-7`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L740-L753
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L740-L753

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.be20Tanner_coboundary_expansion
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    (wordLinearMapTranspose (tannerBoundary q hq40 hq)).SmallSetExpandingAtRelativeRadius
      1 10000000 11 102500 := by sorry
