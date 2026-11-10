-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_copy
-- name    : QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_copy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:13:34.190001+00:00
-- url     : https://prove2.me/theorems/10dc32c8-19bb-43ee-9465-c5b488ebb957
-- title:
--   BDL26 XLocal Connecting Weight: vertical Z image copy
-- statement:
--   The BDL26 XLocal Connecting Weight construction uses the vertical Z image copy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L149-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L149-L153

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalConnectingWeight
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_copy
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (q : Neighbor P x)
    (e : Two × QSubdivisionEdge P q.val S) :
    verticalZ P x S (outputEdge P A x S ⟨q, Sum.inl e⟩) = none := by sorry

attribute [defeq] QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_copy
