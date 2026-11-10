-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_connectingWeight_single_le_of_copied
-- name    : QEC.Coding.BDL26XLocalConnectingWeight.connectingWeight_single_le_of_copied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:24:26.765207+00:00
-- url     : https://prove2.me/theorems/2be533f7-3cff-4c37-80ec-23ecf0213632
-- title:
--   BDL26 XLocal Connecting Weight: connecting Weight single le of copied
-- statement:
--   The BDL26 XLocal Connecting Weight construction uses the connecting Weight single le of copied property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L128-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L128-L135

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalConnectingWeight
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalConnectingWeight.connectingWeight_single_le_of_copied
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S)
    (q : P.Q) (he : copiedQ P x S e = some q) (b : ZMod 2) :
    connectingWeight P A x S (Pi.single e b) ≤ bitWeight b := by sorry
