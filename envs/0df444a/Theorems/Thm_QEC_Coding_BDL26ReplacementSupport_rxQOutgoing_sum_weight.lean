-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxQOutgoing_sum_weight
-- name    : QEC.Coding.BDL26ReplacementSupport.rxQOutgoing_sum_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:36:26.63817+00:00
-- url     : https://prove2.me/theorems/29e08274-cba6-43c7-892d-abae9fdd2dac
-- title:
--   BDL26 Replacement Support: rx QOutgoing sum weight
-- statement:
--   The BDL26 Replacement Support construction uses the rx QOutgoing sum weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L445-L466
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L445-L466

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

theorem QEC.Coding.BDL26ReplacementSupport.rxQOutgoing_sum_weight
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (word : Word Field (QDoubleCylinderVertex P q S)) :
    (∑ z : P.Z, HammingWeight (rxQOutgoing P q S word z)) =
      ∑ z : QStarEdge P q, HammingWeight (rxQZDegreeOne P q z.1 z.2 S word) := by sorry
