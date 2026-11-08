-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzCxH0Coordinates_bijective
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzCxH0Coordinates_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:04:01.180728+00:00
-- url     : https://prove2.me/theorems/c27f45e7-8c3b-4956-bee3-0aaa776ddb33
-- title:
--   BDL26 RZLocal Replacement: rz Cx H0 Coordinates bijective
-- statement:
--   F07 `H⁰(Cx) = 𝔽₂²` as a named bijective coordinate map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16080-L16100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16080-L16100

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzCxH0Coordinates_bijective (P : TannerSquarePresentation) (x : P.X) :
    Function.Bijective (rzCxH0Coordinates P x) := by sorry
