-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_sum_sq_centeredVertexIndicator401
-- name    : QEC.Coding.BalancedProduct.LPSGraph.sum_sq_centeredVertexIndicator401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:03:36.580192+00:00
-- url     : https://prove2.me/theorems/992687da-5324-4b27-9d94-b8850685cab0
-- title:
--   LPSGraph: sum sq centered Vertex Indicator401
-- statement:
--   Squared norm of the division-free centered indicator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L314-L349
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L314-L349

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

theorem QEC.Coding.BalancedProduct.LPSGraph.sum_sq_centeredVertexIndicator401
    (q : ℕ) [Fact q.Prime]
    (S : Finset (PGL(2, ZMod q))) :
    ∑ v, (centeredVertexIndicator401 q S v) ^ 2 =
      (Fintype.card (PGL(2, ZMod q)) : ℝ) * S.card *
        (Fintype.card (PGL(2, ZMod q)) - S.card) := by sorry
