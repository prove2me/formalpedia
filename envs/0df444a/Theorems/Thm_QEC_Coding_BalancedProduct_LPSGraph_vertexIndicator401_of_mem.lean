-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_vertexIndicator401_of_mem
-- name    : QEC.Coding.BalancedProduct.LPSGraph.vertexIndicator401_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:02:54.906118+00:00
-- url     : https://prove2.me/theorems/3a64a312-8462-4173-954c-f64e28d1dfa8
-- title:
--   LPSGraph: vertex Indicator401 of mem
-- statement:
--   The LPSGraph construction uses the vertex Indicator401 of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L207-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L207-L214

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

theorem QEC.Coding.BalancedProduct.LPSGraph.vertexIndicator401_of_mem
    (q : ℕ) [Fact q.Prime]
    (S : Finset (PGL(2, ZMod q)))
    {v : PGL(2, ZMod q)} (hv : v ∈ S) :
    vertexIndicator401 q S v = 1 := by sorry
