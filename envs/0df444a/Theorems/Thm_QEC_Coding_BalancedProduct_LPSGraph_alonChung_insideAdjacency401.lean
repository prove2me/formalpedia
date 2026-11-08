-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_alonChung_insideAdjacency401
-- name    : QEC.Coding.BalancedProduct.LPSGraph.alonChung_insideAdjacency401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:03:58.148903+00:00
-- url     : https://prove2.me/theorems/8122b657-4bae-4994-8b82-887712136d79
-- title:
--   LPSGraph: alon Chung inside Adjacency401
-- statement:
--   Rational Alon--Chung bound obtained from the sole graph-only external
--   premise.  `insideAdjacencyCount401` is directed, so no hidden factor of two is
--   introduced here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L492-L517
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L492-L517

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

theorem QEC.Coding.BalancedProduct.LPSGraph.alonChung_insideAdjacency401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq)
    (S : Finset (PGL(2, ZMod q))) :
    10 * (Fintype.card (PGL(2, ZMod q)) : ℝ) *
        (insideAdjacencyCount401 q hq S : ℝ) ≤
      401 * (S.card : ℝ) *
          ((Fintype.card (PGL(2, ZMod q)) : ℝ) - S.card) +
        4020 * (S.card : ℝ) ^ 2 := by sorry
