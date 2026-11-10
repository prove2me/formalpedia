-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxH0Coordinate_bijective
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCxH0Coordinate_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:44:43.310199+00:00
-- url     : https://prove2.me/theorems/eac4b1c0-d5d3-437e-8701-67283ff87eee
-- title:
--   BDL26 RXLocal Replacement: rx Cx H0 Coordinate bijective
-- statement:
--   F04 `H⁰(Cx)=F₂` as a named bijective coordinate map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21726-L21751
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21726-L21751

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxCxH0Coordinate_bijective (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (x : P.X) (S : OddScale) :
    Function.Bijective (rxCxH0Coordinate P A x S) := by sorry
