-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_eq_on_subdivisionEdge
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_eq_on_subdivisionEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:08:02.406733+00:00
-- url     : https://prove2.me/theorems/96a5ce76-464d-4718-89f4-f5c3572c6ae1
-- title:
--   BDL26 RXLocal Replacement: rx Cx Cocycle eq on subdivision Edge
-- statement:
--   A zero X-cylinder coboundary equates the endpoints of each concrete
--   subdivision edge at a fixed copy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21275-L21294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21275-L21294

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_eq_on_subdivisionEdge
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (copy : Two) (edge : SubdivisionEdge P x S)
    (word : Word Field (DoubleCylinderVertex P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary1 word = 0) :
    word (copy, subdivisionEdgeEnd P x S edge) =
      word (copy, subdivisionEdgeStart P x S edge) := by sorry
