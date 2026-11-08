-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzCzH2Coordinate_bijective_iff_range_eq_totalParity_ker
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzCzH2Coordinate_bijective_iff_range_eq_totalParity_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:59:20.801349+00:00
-- url     : https://prove2.me/theorems/1f6ef1b6-f185-4330-9779-67dba6717b73
-- title:
--   BDL26 RZLocal Replacement: rz Cz H2 Coordinate bijective iff range eq total Parity ker
-- statement:
--   Consequently the exact F07 `H²(Cz) ≃ ᵓ₂` statement is equivalent to
--   the one remaining concrete graph-exactness equality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16783-L16795
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16783-L16795

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzCzH2Coordinate_bijective_iff_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (z : P.Z) (S : OddScale) :
    Function.Bijective (rzCzH2Coordinate P z S) ↔
      LinearMap.range (wordLinearMapTranspose (rzCz P z S).boundary2) =
        LinearMap.ker totalParity := by sorry
