-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzCzH2Coordinate_surjective
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzCzH2Coordinate_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:54:46.426175+00:00
-- url     : https://prove2.me/theorems/9b475304-74b9-49bc-8606-ff82caf65d8d
-- title:
--   BDL26 RZLocal Replacement: rz Cz H2 Coordinate surjective
-- statement:
--   The parity chart is always onto: an existing admissible boundary root gives
--   one concrete cylinder vertex on which to place the requested coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16717-L16732
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16717-L16732

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzCzH2Coordinate_surjective (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (z : P.Z) (S : OddScale) :
    Function.Surjective (rzCzH2Coordinate P z S) := by sorry
