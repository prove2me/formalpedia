-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_adjacencyRayleigh_centeredVertexIndicator401
-- name    : QEC.Coding.BalancedProduct.LPSGraph.adjacencyRayleigh_centeredVertexIndicator401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:03:38.968316+00:00
-- url     : https://prove2.me/theorems/417db663-e12d-4fd1-b210-ddf559712bd3
-- title:
--   LPSGraph: adjacency Rayleigh centered Vertex Indicator401
-- statement:
--   Exact quadratic-form identity for the division-free centered indicator.
--   This is the algebraic bridge from the graph-only Rayleigh premise to induced
--   edge counting.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L399-L487
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L399-L487

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

theorem QEC.Coding.BalancedProduct.LPSGraph.adjacencyRayleigh_centeredVertexIndicator401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (S : Finset (PGL(2, ZMod q))) :
    adjacencyRayleigh401 q hq (centeredVertexIndicator401 q S) =
      (Fintype.card (PGL(2, ZMod q)) : ℝ) ^ 2 *
          insideAdjacencyCount401 q hq S -
        402 * Fintype.card (PGL(2, ZMod q)) * S.card ^ 2 := by sorry
