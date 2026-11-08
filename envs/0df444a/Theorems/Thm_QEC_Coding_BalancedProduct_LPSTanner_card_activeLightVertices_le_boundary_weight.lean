-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_card_activeLightVertices_le_boundary_weight
-- name    : QEC.Coding.BalancedProduct.LPSTanner.card_activeLightVertices_le_boundary_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:24:16.231845+00:00
-- url     : https://prove2.me/theorems/2bcb6fec-6f9e-4aae-bb2c-70d7fa159eab
-- title:
--   LPSTanner: card active Light Vertices le boundary weight
-- statement:
--   Violated checks selected at distinct active vertices are distinct global
--   check coordinates.  Hence the global syndrome weight is at least the number
--   of active light vertices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L574-L601
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L574-L601

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSTanner
open Classical
open GVPlus LPSGenerators LPSGraph
attribute [local instance] QEC.Coding.BalancedProduct.LPSTanner.edge401Fintype

theorem QEC.Coding.BalancedProduct.LPSTanner.card_activeLightVertices_le_boundary_weight
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    (activeLightVertices q hq40 hq x).card ≤
      HammingWeight (tannerBoundary q hq40 hq x) := by sorry
