-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCzH1Coordinate_bijective
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCzH1Coordinate_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:44:20.914263+00:00
-- url     : https://prove2.me/theorems/fde3388b-62fb-4c04-982c-2229bdfcb6c7
-- title:
--   BDL26 RXLocal Replacement: rx Cz H1 Coordinate bijective
-- statement:
--   F06 `H¹(Cz)=0` as a named bijective coordinate map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L24444-L24450
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L24444-L24450

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxCzH1Coordinate_bijective (P : TannerSquarePresentation) (z : P.Z) :
    Function.Bijective (rxCzH1Coordinate P z) := by sorry
