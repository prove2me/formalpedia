-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_vertical
-- name    : QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_vertical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:10:35.35186+00:00
-- url     : https://prove2.me/theorems/8ad5649b-deb2-4736-89e2-989f21f84962
-- title:
--   BDL26 XLocal Connecting Weight: vertical Z image vertical
-- statement:
--   The BDL26 XLocal Connecting Weight construction uses the vertical Z image vertical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L155-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L155-L159

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalConnectingWeight
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_vertical
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (q : Neighbor P x)
    (e : QStarEdge P q.val) :
    verticalZ P x S (outputEdge P A x S ⟨q, Sum.inr e⟩) = some e.val := by sorry

attribute [defeq] QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_vertical
