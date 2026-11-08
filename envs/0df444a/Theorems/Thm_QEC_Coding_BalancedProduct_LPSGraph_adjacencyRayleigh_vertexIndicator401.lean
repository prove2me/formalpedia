-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_adjacencyRayleigh_vertexIndicator401
-- name    : QEC.Coding.BalancedProduct.LPSGraph.adjacencyRayleigh_vertexIndicator401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:03:33.415939+00:00
-- url     : https://prove2.me/theorems/f9abda76-1ab0-4c7a-9757-b60215e2e1d3
-- title:
--   LPSGraph: adjacency Rayleigh vertex Indicator401
-- statement:
--   The LPSGraph construction uses the adjacency Rayleigh vertex Indicator401 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L287-L311
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L287-L311

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

theorem QEC.Coding.BalancedProduct.LPSGraph.adjacencyRayleigh_vertexIndicator401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (S : Finset (PGL(2, ZMod q))) :
    adjacencyRayleigh401 q hq (vertexIndicator401 q S) =
      insideAdjacencyCount401 q hq S := by sorry
