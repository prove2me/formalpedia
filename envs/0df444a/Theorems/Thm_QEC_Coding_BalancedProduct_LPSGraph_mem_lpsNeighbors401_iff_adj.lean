-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_mem_lpsNeighbors401_iff_adj
-- name    : QEC.Coding.BalancedProduct.LPSGraph.mem_lpsNeighbors401_iff_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:03:01.340516+00:00
-- url     : https://prove2.me/theorems/fb99442b-5bed-4fcc-8d65-982e17ce1ff6
-- title:
--   LPSGraph: mem lps Neighbors401 iff adj
-- statement:
--   The LPSGraph construction uses the mem lps Neighbors401 iff adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L81-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L81-L96

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

theorem QEC.Coding.BalancedProduct.LPSGraph.mem_lpsNeighbors401_iff_adj
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (g w : PGL(2, ZMod q)) :
    w ∈ lpsNeighbors401 q hq g ↔
      (lpsCayleyGraph401 q hq).Adj g w := by sorry
