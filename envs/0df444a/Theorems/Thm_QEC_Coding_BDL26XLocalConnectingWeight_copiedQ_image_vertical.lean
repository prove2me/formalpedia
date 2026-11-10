-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_vertical
-- name    : QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_vertical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:10:39.861304+00:00
-- url     : https://prove2.me/theorems/b934d28d-2244-4b69-a47c-0cbf7c2e1229
-- title:
--   BDL26 XLocal Connecting Weight: copied Q image vertical
-- statement:
--   The BDL26 XLocal Connecting Weight construction uses the copied Q image vertical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L96-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L96-L100

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalConnectingWeight
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_vertical
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (q : Neighbor P x)
    (e : QStarEdge P q.val) :
    copiedQ P x S (outputEdge P A x S ⟨q, Sum.inr e⟩) = none := by sorry

attribute [defeq] QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_vertical
