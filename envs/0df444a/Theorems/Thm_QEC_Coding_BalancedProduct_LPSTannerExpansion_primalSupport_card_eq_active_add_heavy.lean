-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_primalSupport_card_eq_active_add_heavy
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.primalSupport_card_eq_active_add_heavy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:30:10.606777+00:00
-- url     : https://prove2.me/theorems/64c94e3d-bd12-4ac2-92d2-2b295f9738e5
-- title:
--   LPSTanner Expansion: primal Support card eq active add heavy
-- statement:
--   The LPSTanner Expansion construction uses the primal Support card eq active add heavy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L311-L347
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L311-L347

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.primalSupport_card_eq_active_add_heavy
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    (primalSupportVertices q hq40 hq x).card =
      (activeLightVertices q hq40 hq x).card +
        (primalHeavyVertices q hq40 hq x).card := by sorry
