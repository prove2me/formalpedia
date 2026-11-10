-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxQZDiagonal_eq_sum_coordinates
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxQZDiagonal_eq_sum_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:23:49.846776+00:00
-- url     : https://prove2.me/theorems/42015ef8-2f11-43c7-8dae-6b70b747fb2b
-- title:
--   BDL26 RXLocal Replacement: rx QZDiagonal eq sum coordinates
-- statement:
--   Aggregating the actual local Q-to-Z quotient maps gives the diagonal of
--   the old Q-Z adjacency coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L24726-L24752
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L24726-L24752

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
universe u

theorem QEC.Coding.BDL26RXLocalReplacement.rxQZDiagonal_eq_sum_coordinates
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (word : Word Field P.Q) (z : P.Z) :
    (rxQZAdjacency P word z, rxQZAdjacency P word z) =
      ∑ q : P.Q, if hqz : P.qz q z = true then
        rxCzH2Coordinates P z
          (rxQZH1ToH2 P q z hqz S (rxAggregateQH1 P q S word))
      else 0 := by sorry
