-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_mem_activeLightVertices_iff
-- name    : QEC.Coding.BalancedProduct.LPSTanner.mem_activeLightVertices_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:23:29.906615+00:00
-- url     : https://prove2.me/theorems/9f2e24e4-2ca8-4698-b19f-45a623a5072a
-- title:
--   LPSTanner: mem active Light Vertices iff
-- statement:
--   The LPSTanner construction uses the mem active Light Vertices iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L559-L569
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L559-L569

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

theorem QEC.Coding.BalancedProduct.LPSTanner.mem_activeLightVertices_iff
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq))
    (g : Vertex401 q) :
    g ∈ activeLightVertices q hq40 hq x ↔
      localView q hq40 hq g x ≠ 0 ∧
        HammingWeight (localView q hq40 hq g x) < 41 := by sorry
