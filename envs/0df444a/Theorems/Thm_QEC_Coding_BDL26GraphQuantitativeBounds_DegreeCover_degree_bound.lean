-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_DegreeCover_degree_bound
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.DegreeCover.degree_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:16:13.191778+00:00
-- url     : https://prove2.me/theorems/1ed0ef22-9f52-4528-a77a-d610304b732e
-- title:
--   Degree Cover: degree bound
-- statement:
--   Degree is bounded by measured same-level, outgoing and incoming neighborhoods.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L505-L538
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L505-L538

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
open QEC.Coding.BDL26GraphQuantitativeBounds.DegreeCover
open MultiscaleDecoder
variable {depth : Nat} {V : LevelIndex depth → Type}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

theorem QEC.Coding.BDL26GraphQuantitativeBounds.DegreeCover.degree_bound (G : DecodingGraphFamily depth V) (u : G.Node) (M : Nat)
    (hlevel : ∀ (i : LevelIndex depth) (x : V i), Nat.card {y : V i // (G.level i).skeleton.adjacent x y} ≤ 7)
    (hup : ∀ (s : StepIndex depth) (x : V s.castSucc), Nat.card {y : V s.succ // G.interLevel s x y = true} ≤ M)
    (hdown : ∀ (s : StepIndex depth) (y : V s.succ), Nat.card {x : V s.castSucc // G.interLevel s x y = true} ≤ 1) :
    Nat.card {v : G.Node // G.adjacent u v} ≤ M + 8 := by sorry
