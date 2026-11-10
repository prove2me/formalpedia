-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxBoundary2Matrix_decomposition
-- name    : QEC.Coding.BDL26ReplacementSupport.rxBoundary2Matrix_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:35:16.140715+00:00
-- url     : https://prove2.me/theorems/b924394c-9963-48ff-9bdd-e23082f64232
-- title:
--   BDL26 Replacement Support: rx Boundary2 Matrix decomposition
-- statement:
--   The BDL26 Replacement Support construction uses the rx Boundary2 Matrix decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L201-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L201-L209

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

theorem QEC.Coding.BDL26ReplacementSupport.rxBoundary2Matrix_decomposition (P : TannerSquarePresentation) (S : OddScale) :
    rxBoundary2Matrix P S = rxLocalBoundary2Matrix P S +
      rxXQBoundary2Matrix P S + rxQZBoundary2Matrix P S := by sorry
