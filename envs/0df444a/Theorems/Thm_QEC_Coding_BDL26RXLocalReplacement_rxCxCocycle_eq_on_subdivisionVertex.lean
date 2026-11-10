-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_eq_on_subdivisionVertex
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_eq_on_subdivisionVertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:21:37.226411+00:00
-- url     : https://prove2.me/theorems/e583af41-a174-476c-998b-a6aa1d67c0fa
-- title:
--   BDL26 RXLocal Replacement: rx Cx Cocycle eq on subdivision Vertex
-- statement:
--   Every normalized subdivision vertex has the common boundary-root value.
--   The face-owner existential for old/edge tags is consumed only in the preceding
--   Prop proofs; this theorem returns no selected face or path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21613-L21663
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21613-L21663

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_eq_on_subdivisionVertex
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (copy : Two)
    (word : Word Field (DoubleCylinderVertex P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary1 word = 0)
    (vertex : SubdivisionVertex P x S) :
    word (copy, vertex) =
      word (copy,
        (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1) := by sorry
