-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzCzH2Coordinate_injective_iff_range_eq_totalParity_ker
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzCzH2Coordinate_injective_iff_range_eq_totalParity_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:54:14.401353+00:00
-- url     : https://prove2.me/theorems/ea34b0cf-c582-47ce-9989-09a375e25802
-- title:
--   BDL26 RZLocal Replacement: rz Cz H2 Coordinate injective iff range eq total Parity ker
-- statement:
--   Exact reduction of the remaining F07 injectivity obligation.  Quotient
--   extensionality proves injectivity precisely when the concrete top coboundary
--   fills the even-parity kernel; no representative selector is introduced.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16737-L16779
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16737-L16779

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzCzH2Coordinate_injective_iff_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :
    Function.Injective (rzCzH2Coordinate P z S) ↔
      LinearMap.range (wordLinearMapTranspose (rzCz P z S).boundary2) =
        LinearMap.ker totalParity := by sorry
