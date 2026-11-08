-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_vertexIndicator401_of_not_mem
-- name    : QEC.Coding.BalancedProduct.LPSGraph.vertexIndicator401_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:03:03.839217+00:00
-- url     : https://prove2.me/theorems/395149ed-5221-4dd6-84ca-e47f119dfa1d
-- title:
--   LPSGraph: vertex Indicator401 of not mem
-- statement:
--   The LPSGraph construction uses the vertex Indicator401 of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L216-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L216-L223

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

theorem QEC.Coding.BalancedProduct.LPSGraph.vertexIndicator401_of_not_mem
    (q : ℕ) [Fact q.Prime]
    (S : Finset (PGL(2, ZMod q)))
    {v : PGL(2, ZMod q)} (hv : v ∉ S) :
    vertexIndicator401 q S v = 0 := by sorry
