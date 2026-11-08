-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_upperUnipotent_edge_fixed_iff_one
-- name    : QEC.Coding.BalancedProduct.LPSGraph.upperUnipotent_edge_fixed_iff_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:04:04.018076+00:00
-- url     : https://prove2.me/theorems/087f4b52-10a6-46f7-9e92-9ea313b10c5e
-- title:
--   LPSGraph: upper Unipotent edge fixed iff one
-- statement:
--   The upper-unipotent right action is free on genuine unoriented LPS edges.
--   The endpoint-preserving branch reduces to vertex freeness.  The endpoint-swap
--   branch would put an LPS generator in a conjugate of the upper-unipotent
--   subgroup, contradicting the proved determinant square class.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L141-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L141-L167

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

theorem QEC.Coding.BalancedProduct.LPSGraph.upperUnipotent_edge_fixed_iff_one
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    {g w : PGL(2, ZMod q)}
    (hgw : (lpsCayleyGraph401 q hq).Adj g w)
    (h : upperUnipotentSubgroup (R := ZMod q)) :
    s(g * (h : PGL(2, ZMod q)), w * (h : PGL(2, ZMod q))) = s(g, w) ↔
      h = 1 := by sorry
