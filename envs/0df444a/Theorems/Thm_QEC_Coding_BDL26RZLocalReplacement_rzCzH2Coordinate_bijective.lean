-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzCzH2Coordinate_bijective
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzCzH2Coordinate_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:04:36.042066+00:00
-- url     : https://prove2.me/theorems/926f702d-121d-4c11-ac65-278cbc0055f0
-- title:
--   BDL26 RZLocal Replacement: rz Cz H2 Coordinate bijective
-- statement:
--   Exact F07 degree-two chart for the concrete dual Z block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16815-L16820
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16815-L16820

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzCzH2Coordinate_bijective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (z : P.Z) (S : OddScale) :
    Function.Bijective (rzCzH2Coordinate P z S) := by sorry
