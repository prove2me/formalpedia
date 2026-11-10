-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_copy_one_eq_zero_at_boundaryRoot
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_copy_one_eq_zero_at_boundaryRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:21:39.131742+00:00
-- url     : https://prove2.me/theorems/02dbe331-f088-4b13-ad10-e8e26238e921
-- title:
--   BDL26 RXLocal Replacement: rx Cx Cocycle copy one eq zero at boundary Root
-- statement:
--   The boundary-root vertical cylinder edge identifies the two copies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21666-L21687
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21666-L21687

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_copy_one_eq_zero_at_boundaryRoot
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderVertex P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary1 word = 0) :
    word (1,
        (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1) =
      word (0,
        (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1) := by sorry
