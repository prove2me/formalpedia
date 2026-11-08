-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_lpsCayleyGraph401_degree
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.lpsCayleyGraph401_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:29:32.24604+00:00
-- url     : https://prove2.me/theorems/57e1ebad-13ea-4df3-bbf7-7f21e7217569
-- title:
--   LPSTanner Expansion: lps Cayley Graph401 degree
-- statement:
--   Every concrete LPS vertex has degree exactly 402.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L173-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L173-L183

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.lpsCayleyGraph401_degree
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : Vertex401 q) :
    (lpsCayleyGraph401 q hq).degree g = 402 := by sorry
