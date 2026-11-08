-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_sum_neighbor_vertexIndicator401
-- name    : QEC.Coding.BalancedProduct.LPSGraph.sum_neighbor_vertexIndicator401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:02:56.970211+00:00
-- url     : https://prove2.me/theorems/a559eb16-b808-4592-b8fa-da5e11d647fb
-- title:
--   LPSGraph: sum neighbor vertex Indicator401
-- statement:
--   The LPSGraph construction uses the sum neighbor vertex Indicator401 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L272-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L272-L285

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

theorem QEC.Coding.BalancedProduct.LPSGraph.sum_neighbor_vertexIndicator401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (S : Finset (PGL(2, ZMod q)))
    (v : PGL(2, ZMod q)) :
    ∑ w ∈ lpsNeighbors401 q hq v, vertexIndicator401 q S w =
      (lpsNeighborsIn401 q hq S v).card := by sorry
