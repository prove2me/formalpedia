-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_dualSupport_card_eq_exposed_add_unexposed
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.dualSupport_card_eq_exposed_add_unexposed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:31:30.858252+00:00
-- url     : https://prove2.me/theorems/dba82c0b-9234-4302-9661-ca3a838ae375
-- title:
--   LPSTanner Expansion: dual Support card eq exposed add unexposed
-- statement:
--   The LPSTanner Expansion construction uses the dual Support card eq exposed add unexposed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L633-L666
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L633-L666

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.dualSupport_card_eq_exposed_add_unexposed
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q)) :
    (dualSupportVertices q y).card =
      (dualExposedVertices q hq40 hq y).card +
        (dualUnexposedSupportVertices q hq40 hq y).card := by sorry
