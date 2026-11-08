-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0DoubleCylinderEdge_card
-- name    : QEC.Coding.BDL26TannerLocalRegularity.baseQ0DoubleCylinderEdge_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:33:07.434879+00:00
-- url     : https://prove2.me/theorems/04bd36c7-8b02-4d32-9b92-93e03bfb6d97
-- title:
--   BDL26 Tanner Local Regularity: base Q0 Double Cylinder Edge card
-- statement:
--   The BDL26 Tanner Local Regularity construction uses the base Q0 Double Cylinder Edge card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3197-L3200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3197-L3200

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26TannerLocalRegularity
open Module
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
universe u

theorem QEC.Coding.BDL26TannerLocalRegularity.baseQ0DoubleCylinderEdge_card :
    Fintype.card (QDoubleCylinderEdge baseTannerSquarePresentation
      (0 : BaseQubit) scaleFive) = 5 := by sorry
