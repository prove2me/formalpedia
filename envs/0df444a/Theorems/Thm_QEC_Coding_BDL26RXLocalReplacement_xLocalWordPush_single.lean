-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalWordPush_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:21:10.54302+00:00
-- url     : https://prove2.me/theorems/994cd941-58eb-4335-831f-a6e3c17bb097
-- title:
--   BDL26 RXLocal Replacement: x Local Word Push single
-- statement:
--   The BDL26 RXLocal Replacement construction uses the x Local Word Push single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L418-L427
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L418-L427

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalWordPush_single
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (embed : I → J) (i : I) (b : Field) :
    xLocalWordPush embed (Pi.single i b) = Pi.single (embed i) b := by sorry
