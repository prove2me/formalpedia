-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_card_dualExposedVertices_le_transpose_weight
-- name    : QEC.Coding.BalancedProduct.LPSTanner.card_dualExposedVertices_le_transpose_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:24:25.308523+00:00
-- url     : https://prove2.me/theorems/3a263b80-29ae-4f14-a3e6-5731219218ee
-- title:
--   LPSTanner: card dual Exposed Vertices le transpose weight
-- statement:
--   Exposure witnesses at distinct supported vertices select distinct global
--   edges, and every selected edge is nonzero in the global transpose.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L843-L882
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L843-L882

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

theorem QEC.Coding.BalancedProduct.LPSTanner.card_dualExposedVertices_le_transpose_weight
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q)) :
    (dualExposedVertices q hq40 hq y).card ≤
      HammingWeight
        (wordLinearMapTranspose (tannerBoundary q hq40 hq) y) := by sorry
