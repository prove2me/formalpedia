-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzCzTopCoboundary_range_eq_totalParity_ker
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzCzTopCoboundary_range_eq_totalParity_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:58:09.343047+00:00
-- url     : https://prove2.me/theorems/f174a654-e188-4532-bb2c-d3c815fbf572
-- title:
--   BDL26 RZLocal Replacement: rz Cz Top Coboundary range eq total Parity ker
-- statement:
--   The materialized Z-cylinder top coboundary fills exactly the even-parity
--   words.  Connectivity is assembled locally from rectangle segments and the
--   existing admissible boundary root; no path selector is retained.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16800-L16812
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16800-L16812

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzCzTopCoboundary_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (z : P.Z) (S : OddScale) :
    LinearMap.range (wordLinearMapTranspose (rzCz P z S).boundary2) =
      LinearMap.ker totalParity := by sorry
