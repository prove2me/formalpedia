-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCzH2Coordinates_bijective
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCzH2Coordinates_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:44:51.256609+00:00
-- url     : https://prove2.me/theorems/9b27f740-e0b2-4717-ae92-6f2409c635c8
-- title:
--   BDL26 RXLocal Replacement: rx Cz H2 Coordinates bijective
-- statement:
--   F06 `H²(Cz)=F₂²` as a named bijective coordinate map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L24509-L24530
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L24509-L24530

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

theorem QEC.Coding.BDL26RXLocalReplacement.rxCzH2Coordinates_bijective (P : TannerSquarePresentation) (z : P.Z) :
    Function.Bijective (rxCzH2Coordinates P z) := by sorry
