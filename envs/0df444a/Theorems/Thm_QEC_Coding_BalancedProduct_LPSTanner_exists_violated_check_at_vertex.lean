-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_exists_violated_check_at_vertex
-- name    : QEC.Coding.BalancedProduct.LPSTanner.exists_violated_check_at_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:24:15.101481+00:00
-- url     : https://prove2.me/theorems/2b8a4f46-285c-49cc-903a-c29ba9331494
-- title:
--   LPSTanner: exists violated check at vertex
-- statement:
--   If the labelled restriction of an edge word at `g` is nonzero and has
--   fewer than 41 nonzero incident edges, then at least one of the 200 Tanner
--   checks at `g` is violated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L529-L545
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L529-L545

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

theorem QEC.Coding.BalancedProduct.LPSTanner.exists_violated_check_at_vertex
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq))
    (g : Vertex401 q)
    (hlocal0 : localView q hq40 hq g x ≠ 0)
    (hlocalWeight : HammingWeight (localView q hq40 hq g x) < 41) :
    ∃ j : Fin 200, tannerBoundary q hq40 hq x (g, j) ≠ 0 := by sorry
