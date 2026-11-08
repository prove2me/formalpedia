-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_card_lpsNeighbors401
-- name    : QEC.Coding.BalancedProduct.LPSGraph.card_lpsNeighbors401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:02:54.249698+00:00
-- url     : https://prove2.me/theorems/74709310-a781-4d3a-ae5d-a10566cc5833
-- title:
--   LPSGraph: card lps Neighbors401
-- statement:
--   The LPSGraph construction uses the card lps Neighbors401 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L98-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean#L98-L108

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

theorem QEC.Coding.BalancedProduct.LPSGraph.card_lpsNeighbors401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : PGL(2, ZMod q)) :
    (lpsNeighbors401 q hq g).card = 402 := by sorry
