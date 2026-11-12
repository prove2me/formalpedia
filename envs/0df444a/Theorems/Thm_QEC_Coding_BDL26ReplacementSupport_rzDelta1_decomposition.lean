-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rzDelta1_decomposition
-- name    : QEC.Coding.BDL26ReplacementSupport.rzDelta1_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:59:14.243487+00:00
-- url     : https://prove2.me/theorems/d575d1d5-ac34-4277-be64-a9b0c9ec24cd
-- title:
--   BDL26 Replacement Support: rz Delta1 decomposition
-- statement:
--   Exact RZ local/connecting decomposition on the materialized presentation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L375-L391
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L375-L391

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26ReplacementSupport.rzDelta1_decomposition
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) :
    tannerCoboundary1 (rzReplacementPresentation P A4.toTannerSquareAdmissible S) =
      rzLocalDelta1 P A4.toTannerSquareAdmissible S +
        rzConnectingQZ1 P A4.toTannerSquareAdmissible S := by sorry
