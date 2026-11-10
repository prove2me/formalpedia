-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_eq_on_boundaryVertex
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_eq_on_boundaryVertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:07:42.089666+00:00
-- url     : https://prove2.me/theorems/3043470d-028f-4c2e-abce-dd632a1d5e12
-- title:
--   BDL26 RXLocal Replacement: rx Cx Cocycle eq on boundary Vertex
-- statement:
--   A zero X-cylinder coboundary is constant on every old boundary vertex at
--   one fixed cylinder copy.  This uses only the supplied historical boundary
--   path; it does not select an incident face or a quotient representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21387-L21443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21387-L21443

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_eq_on_boundaryVertex
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (copy : Two)
    (word : Word Field (DoubleCylinderVertex P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary1 word = 0)
    (vertex : XStarBoundaryVertex P x) :
    word (copy, (subdivisionOriginalBoundaryVertex P x S vertex).1) =
      word (copy,
        (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1) := by sorry
