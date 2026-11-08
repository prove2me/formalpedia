-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzAggregateQZH1ToH2_coordinate
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzAggregateQZH1ToH2_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:00:59.720942+00:00
-- url     : https://prove2.me/theorems/383e86d1-518f-4cac-b350-bd54c13bae08
-- title:
--   BDL26 RZLocal Replacement: rz Aggregate QZH1 To H2 coordinate
-- statement:
--   F09 aggregate Q-Z formula: in the named F07 charts, the actual quotient
--   map is exactly the old Tanner Q-Z adjacency coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17247-L17263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17247-L17263

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzAggregateQZH1ToH2_coordinate (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale)
    (classes : RZLocalH1 P S) (z : P.Z) :
    rzCzH2Coordinate P z S (rzAggregateQZH1ToH2 P A S classes z) =
      ∑ q : P.Q, if hqz : P.qz q z = true then
        rzCqH1Coordinate P q S (classes q)
      else 0 := by sorry
