-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_card_check401_eq
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.card_check401_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:29:15.203785+00:00
-- url     : https://prove2.me/theorems/b73c027c-f2a1-4642-945b-b1664b314f95
-- title:
--   LPSTanner Expansion: card check401 eq
-- statement:
--   The LPSTanner Expansion construction uses the card check401 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L699-L702
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L699-L702

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.card_check401_eq
    (q : ℕ) [Fact q.Prime] :
    Fintype.card (Check401 q) = 200 * Fintype.card (Vertex401 q) := by sorry
