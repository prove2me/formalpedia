-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_dualSupportedNeighbors_subset_lps
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.dualSupportedNeighbors_subset_lps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:30:45.281975+00:00
-- url     : https://prove2.me/theorems/57c87efb-c878-4c64-9f51-adf34752dbdc
-- title:
--   LPSTanner Expansion: dual Supported Neighbors subset lps
-- statement:
--   The LPSTanner Expansion construction uses the dual Supported Neighbors subset lps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L536-L546
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L536-L546

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.dualSupportedNeighbors_subset_lps
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q) :
    dualSupportedNeighbors q hq40 hq y g ⊆ lpsNeighbors401 q hq g := by sorry
