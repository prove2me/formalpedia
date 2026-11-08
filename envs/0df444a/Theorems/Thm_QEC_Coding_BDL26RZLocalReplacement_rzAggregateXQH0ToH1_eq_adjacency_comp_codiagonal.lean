-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzAggregateXQH0ToH1_eq_adjacency_comp_codiagonal
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzAggregateXQH0ToH1_eq_adjacency_comp_codiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:04:51.867797+00:00
-- url     : https://prove2.me/theorems/01182640-64e6-4a73-9447-90eb042fe823
-- title:
--   BDL26 RZLocal Replacement: rz Aggregate XQH0 To H1 eq adjacency comp codiagonal
-- statement:
--   F09 as an equality of actual aggregate linear maps:
--   `H(g_XQ⁰) = δ⁰ ∘ Δ′`, with the two auxiliary summands killed by the
--   same left-hand map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17201-L17218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17201-L17218

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzAggregateXQH0ToH1_eq_adjacency_comp_codiagonal
    (P : TannerSquarePresentation) (S : OddScale) :
    (rzAggregateQCoordinates P S).comp (rzAggregateXQH0ToH1 P S) =
      (rzXQAdjacencyCoboundary P).comp
        ((rzPointwiseCodiagonal P).comp (rzAggregateXCoordinates P S)) := by sorry
