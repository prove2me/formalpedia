-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_eq_on_edgeInterior
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_eq_on_edgeInterior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:07:49.903187+00:00
-- url     : https://prove2.me/theorems/30b93c60-8f7f-46c9-965f-e06b50528d5c
-- title:
--   BDL26 RXLocal Replacement: rx Cx Cocycle eq on edge Interior
-- statement:
--   Every path-interior subdivision tag has the common boundary-root value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21566-L21608
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21566-L21608

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_eq_on_edgeInterior
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (copy : Two)
    (word : Word Field (DoubleCylinderVertex P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary1 word = 0)
    (edge : XStarEdge P x) (index : Fin (S.half - 1)) :
    word (copy, Sum.inr (Sum.inl (edge, index))) =
      word (copy,
        (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1) := by sorry
