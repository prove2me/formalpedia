-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_HammingWeight_eq_sum_checkBlock
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.HammingWeight_eq_sum_checkBlock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:29:29.362993+00:00
-- url     : https://prove2.me/theorems/2cb11e36-4fc6-4a9c-8a74-428bf2a2fcab
-- title:
--   LPSTanner Expansion: Hamming Weight eq sum check Block
-- statement:
--   The LPSTanner Expansion construction uses the Hamming Weight eq sum check Block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L433-L441
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L433-L441

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.HammingWeight_eq_sum_checkBlock
    (q : ℕ) [Fact q.Prime]
    (y : Word (ZMod 2) (Check401 q)) :
    HammingWeight y = ∑ g, HammingWeight (checkBlock q g y) := by sorry
