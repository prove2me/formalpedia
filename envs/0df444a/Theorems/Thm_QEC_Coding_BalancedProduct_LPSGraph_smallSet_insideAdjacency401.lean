-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_smallSet_insideAdjacency401
-- name    : QEC.Coding.BalancedProduct.LPSGraph.smallSet_insideAdjacency401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:03:05.246873+00:00
-- url     : https://prove2.me/theorems/7828894c-a500-42a1-8428-5e7f9d0641d4
-- title:
--   LPSGraph: small Set inside Adjacency401
-- statement:
--   At the corrected BE20 primal graph radius, the induced directed adjacency
--   count is strictly below `41 |S|`.  The rational constant `1003/25 = 40.12`
--   leaves visible slack above the LPS contribution `40.1`; no decimal arithmetic
--   or source normalization identity is hidden in the proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L523-L547
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L523-L547

import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Real.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSGraph
open Matrix
open LPSArithmetic LPSGenerators

theorem QEC.Coding.BalancedProduct.LPSGraph.smallSet_insideAdjacency401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq)
    (S : Finset (PGL(2, ZMod q)))
    (hsmall : 10000000 * S.card ≤
      402 * Fintype.card (PGL(2, ZMod q))) :
    25 * insideAdjacencyCount401 q hq S ≤ 1003 * S.card := by sorry
