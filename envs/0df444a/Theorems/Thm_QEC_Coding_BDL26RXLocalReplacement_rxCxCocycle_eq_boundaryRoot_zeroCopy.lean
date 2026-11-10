-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_eq_boundaryRoot_zeroCopy
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_eq_boundaryRoot_zeroCopy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:10:59.78964+00:00
-- url     : https://prove2.me/theorems/3e184a19-c517-45ea-947b-e9e55845c00d
-- title:
--   BDL26 RXLocal Replacement: rx Cx Cocycle eq boundary Root zero Copy
-- statement:
--   Every X-cylinder degree-zero cocycle is constant at the copy-zero
--   boundary root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21691-L21706
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21691-L21706

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_eq_boundaryRoot_zeroCopy
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderVertex P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary1 word = 0)
    (vertex : DoubleCylinderVertex P x S) :
    word vertex =
      word (0,
        (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1) := by sorry
