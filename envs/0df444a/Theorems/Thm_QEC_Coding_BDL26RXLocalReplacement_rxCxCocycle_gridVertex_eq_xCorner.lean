-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_gridVertex_eq_xCorner
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_gridVertex_eq_xCorner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:07:44.842682+00:00
-- url     : https://prove2.me/theorems/a44b068a-ff52-4c7a-85d8-03483d56c680
-- title:
--   BDL26 RXLocal Replacement: rx Cx Cocycle grid Vertex eq x Corner
-- statement:
--   Every grid vertex of one materialized local face has the value of its
--   X-corner under a zero X-cylinder coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21341-L21360
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21341-L21360

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_gridVertex_eq_xCorner
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (copy : Two) (face : XStarFace P x)
    (i j : Fin (S.half + 1))
    (word : Word Field (DoubleCylinderVertex P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary1 word = 0) :
    word (copy, subdivisionGridVertex P x S face i j) =
      word (copy, Sum.inl (xStarFaceXVertex P x face)) := by sorry
