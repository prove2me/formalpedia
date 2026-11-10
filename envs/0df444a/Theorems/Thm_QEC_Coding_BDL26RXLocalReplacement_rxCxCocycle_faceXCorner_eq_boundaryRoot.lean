-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_faceXCorner_eq_boundaryRoot
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_faceXCorner_eq_boundaryRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:07:53.050095+00:00
-- url     : https://prove2.me/theorems/e74249ab-f63e-4e96-9379-8ceac0812219
-- title:
--   BDL26 RXLocal Replacement: rx Cx Cocycle face XCorner eq boundary Root
-- statement:
--   The X-corner of every materialized old face has the common boundary-root
--   value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21447-L21472
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21447-L21472

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_faceXCorner_eq_boundaryRoot
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (copy : Two) (face : XStarFace P x)
    (word : Word Field (DoubleCylinderVertex P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary1 word = 0) :
    word (copy, Sum.inl (xStarFaceXVertex P x face)) =
      word (copy,
        (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1) := by sorry
