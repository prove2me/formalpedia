-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzAggregateQZH1ToH2_eq_adjacency
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzAggregateQZH1ToH2_eq_adjacency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:07:28.989939+00:00
-- url     : https://prove2.me/theorems/1767f5a7-6499-47ad-b926-592759b41a0d
-- title:
--   BDL26 RZLocal Replacement: rz Aggregate QZH1 To H2 eq adjacency
-- statement:
--   F09 as an equality of actual aggregate linear maps:
--   `H(g_QZ¹) = δ¹` in the named F07 parity charts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17267-L17284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17267-L17284

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzAggregateQZH1ToH2_eq_adjacency
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) :
    (rzAggregateZCoordinates P S).comp (rzAggregateQZH1ToH2 P A S) =
      (rzQZAdjacencyCoboundary P).comp (rzAggregateQCoordinates P S) := by sorry
