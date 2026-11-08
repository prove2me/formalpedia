-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_mem_dualExposedVertices_iff
-- name    : QEC.Coding.BalancedProduct.LPSTanner.mem_dualExposedVertices_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:23:21.363204+00:00
-- url     : https://prove2.me/theorems/5ce19e65-36aa-453a-80a5-3bad396e1bf7
-- title:
--   LPSTanner: mem dual Exposed Vertices iff
-- statement:
--   The LPSTanner construction uses the mem dual Exposed Vertices iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L830-L839
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L830-L839

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

theorem QEC.Coding.BalancedProduct.LPSTanner.mem_dualExposedVertices_iff
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q) :
    g ∈ dualExposedVertices q hq40 hq y ↔
      Nonempty (DualExposureWitness q hq40 hq y g) := by sorry
