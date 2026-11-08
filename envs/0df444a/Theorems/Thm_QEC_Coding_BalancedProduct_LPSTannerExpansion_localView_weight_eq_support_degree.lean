-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_localView_weight_eq_support_degree
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.localView_weight_eq_support_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:29:35.797505+00:00
-- url     : https://prove2.me/theorems/4331fe33-bfc9-4c26-bcd8-3977cf577b99
-- title:
--   LPSTanner Expansion: local View weight eq support degree
-- statement:
--   The LPSTanner Expansion construction uses the local View weight eq support degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L148-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L148-L158

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.localView_weight_eq_support_degree
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq))
    (g : Vertex401 q) :
    HammingWeight (localView q hq40 hq g x) =
      (wordSupportGraph q hq x).degree g := by sorry
