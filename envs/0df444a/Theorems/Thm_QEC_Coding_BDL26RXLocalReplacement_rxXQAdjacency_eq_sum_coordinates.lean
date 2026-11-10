-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxXQAdjacency_eq_sum_coordinates
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxXQAdjacency_eq_sum_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:23:43.039191+00:00
-- url     : https://prove2.me/theorems/9ccd9d80-0e49-4a25-83ff-d8338cc6064f
-- title:
--   BDL26 RXLocal Replacement: rx XQAdjacency eq sum coordinates
-- statement:
--   Aggregating the actual local X-to-Q quotient maps recovers precisely the
--   old X-Q adjacency map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L24679-L24692
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L24679-L24692

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxXQAdjacency_eq_sum_coordinates
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (word : Word Field P.X) (q : P.Q) :
    rxXQAdjacency P word q =
      ∑ x : P.X, if hxq : P.xq x q = true then
        rxCqH1Coordinate P q S
          (rxXQH0ToH1 P A q x hxq S (rxAggregateXH0 P x S word))
      else 0 := by sorry
