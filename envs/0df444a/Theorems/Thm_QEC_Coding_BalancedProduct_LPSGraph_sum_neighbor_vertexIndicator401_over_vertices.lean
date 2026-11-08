-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_sum_neighbor_vertexIndicator401_over_vertices
-- name    : QEC.Coding.BalancedProduct.LPSGraph.sum_neighbor_vertexIndicator401_over_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:03:38.638051+00:00
-- url     : https://prove2.me/theorems/cbe7f4b8-072a-4390-afb2-c0223d6cca64
-- title:
--   LPSGraph: sum neighbor vertex Indicator401 over vertices
-- statement:
--   Total incidence into `S`: regularity and symmetry make it `402 |S|`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L367-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L367-L394

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

theorem QEC.Coding.BalancedProduct.LPSGraph.sum_neighbor_vertexIndicator401_over_vertices
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (S : Finset (PGL(2, ZMod q))) :
    ∑ v, ∑ w ∈ lpsNeighbors401 q hq v, vertexIndicator401 q S w =
      402 * S.card := by sorry
