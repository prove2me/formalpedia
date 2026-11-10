-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCqH1Coordinate_bijective
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCqH1Coordinate_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:21:39.212862+00:00
-- url     : https://prove2.me/theorems/3cbd736b-4888-4500-82a0-e18e9f242242
-- title:
--   BDL26 RXLocal Replacement: rx Cq H1 Coordinate bijective
-- statement:
--   F06 `H¹(Cq)=F₂` as a named bijective coordinate map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L24375-L24413
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L24375-L24413

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxCqH1Coordinate_bijective (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (S : OddScale) :
    Function.Bijective (rxCqH1Coordinate P q S) := by sorry
