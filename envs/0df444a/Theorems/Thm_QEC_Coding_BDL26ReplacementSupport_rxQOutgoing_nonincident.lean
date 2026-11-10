-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxQOutgoing_nonincident
-- name    : QEC.Coding.BDL26ReplacementSupport.rxQOutgoing_nonincident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:16:07.244509+00:00
-- url     : https://prove2.me/theorems/8117c1c1-0bef-451f-9a90-070c3239caf7
-- title:
--   BDL26 Replacement Support: rx QOutgoing nonincident
-- statement:
--   The BDL26 Replacement Support construction uses the rx QOutgoing nonincident property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L439-L443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L439-L443

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

theorem QEC.Coding.BDL26ReplacementSupport.rxQOutgoing_nonincident
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (word : Word Field (QDoubleCylinderVertex P q S))
    (z : P.Z) (hz : P.qz q z ≠ true) : rxQOutgoing P q S word z = 0 := by sorry
