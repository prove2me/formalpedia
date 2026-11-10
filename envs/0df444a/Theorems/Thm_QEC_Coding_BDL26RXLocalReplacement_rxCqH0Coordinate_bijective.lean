-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCqH0Coordinate_bijective
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCqH0Coordinate_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:44:52.390426+00:00
-- url     : https://prove2.me/theorems/fa354f78-e048-4f9c-a7cd-8f43b915bb98
-- title:
--   BDL26 RXLocal Replacement: rx Cq H0 Coordinate bijective
-- statement:
--   F06 `H⁰(Cq)=0` as a named bijective coordinate map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L24285-L24292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L24285-L24292

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxCqH0Coordinate_bijective (P : TannerSquarePresentation)
    (q : P.Q) (S : OddScale) :
    Function.Bijective (rxCqH0Coordinate P q S) := by sorry
