-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzAggregateXQH0ToH1_coordinate
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzAggregateXQH0ToH1_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:58:29.755769+00:00
-- url     : https://prove2.me/theorems/4f006295-f0e1-4fd3-ab8e-8d270a174fbb
-- title:
--   BDL26 RZLocal Replacement: rz Aggregate XQH0 To H1 coordinate
-- statement:
--   F09 aggregate X-Q formula: after the named F07 charts, the actual quotient
--   map is old Tanner adjacency after pointwise codiagonal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17180-L17196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17180-L17196

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzAggregateXQH0ToH1_coordinate (P : TannerSquarePresentation)
    (S : OddScale) (classes : RZLocalH0 P S) (q : P.Q) :
    rzCqH1Coordinate P q S (rzAggregateXQH0ToH1 P S classes q) =
      ∑ x : P.X, if hxq : P.xq x q = true then
        (rzCxH0Coordinates P x (classes.2.1 x)).1 +
          (rzCxH0Coordinates P x (classes.2.1 x)).2
      else 0 := by sorry
