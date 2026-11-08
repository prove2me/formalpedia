-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_sum_lpsNeighbors401_eq_sum_generators
-- name    : QEC.Coding.BalancedProduct.LPSGraph.sum_lpsNeighbors401_eq_sum_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:03:36.19121+00:00
-- url     : https://prove2.me/theorems/68583898-cf1e-4f14-87c8-e9e920193605
-- title:
--   LPSGraph: sum lps Neighbors401 eq sum generators
-- statement:
--   Summing over the explicit neighbor image is the same as summing over the
--   402 generators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L353-L364
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L353-L364

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

theorem QEC.Coding.BalancedProduct.LPSGraph.sum_lpsNeighbors401_eq_sum_generators
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (v : PGL(2, ZMod q))
    (f : PGL(2, ZMod q) → ℝ) :
    ∑ w ∈ lpsNeighbors401 q hq v, f w =
      ∑ s ∈ lpsGenerators401 q hq, f (s * v) := by sorry
