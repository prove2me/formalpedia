-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_be20Tanner_boundary_expansion
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.be20Tanner_boundary_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:29:51.859571+00:00
-- url     : https://prove2.me/theorems/4bfae2b1-ea39-4944-9350-32c27ca4b9c8
-- title:
--   LPSTanner Expansion: be20 Tanner boundary expansion
-- statement:
--   Concrete primal BE20 Tanner expansion at the owner-approved repaired
--   radius `10^-7`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L409-L422
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L409-L422

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.be20Tanner_boundary_expansion
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    (tannerBoundary q hq40 hq).SmallSetExpandingAtRelativeRadius
      1 10000000 44 41123 := by sorry
