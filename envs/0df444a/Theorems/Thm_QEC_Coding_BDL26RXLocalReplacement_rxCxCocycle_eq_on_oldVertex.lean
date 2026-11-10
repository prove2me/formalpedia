-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_eq_on_oldVertex
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_eq_on_oldVertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:07:03.109384+00:00
-- url     : https://prove2.me/theorems/62f38db6-677d-4021-8758-d178e62698b9
-- title:
--   BDL26 RXLocal Replacement: rx Cx Cocycle eq on old Vertex
-- statement:
--   Every original X-star vertex has the common boundary-root value.  Face
--   membership existentials are eliminated only inside this proposition proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21476-L21563
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21476-L21563

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_eq_on_oldVertex
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (copy : Two)
    (word : Word Field (DoubleCylinderVertex P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary1 word = 0)
    (vertex : XStarVertex P x) :
    word (copy, Sum.inl vertex) =
      word (copy,
        (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1) := by sorry
