-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_eq_on_starEdge
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_eq_on_starEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:08:14.370778+00:00
-- url     : https://prove2.me/theorems/e27600bb-674b-4e82-82ef-fb01c05e71f8
-- title:
--   BDL26 RXLocal Replacement: rx Cx Cocycle eq on star Edge
-- statement:
--   A zero X-cylinder coboundary equates the two ends of every subdivided
--   original star edge, at either fixed cylinder copy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21243-L21271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21243-L21271

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_eq_on_starEdge
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (copy : Two) (edge : XStarEdge P x)
    (word : Word Field (DoubleCylinderVertex P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary1 word = 0) :
    word (copy, Sum.inl (xStarEdgeEnd P x edge)) =
      word (copy, Sum.inl (xStarEdgeStart P x edge)) := by sorry
