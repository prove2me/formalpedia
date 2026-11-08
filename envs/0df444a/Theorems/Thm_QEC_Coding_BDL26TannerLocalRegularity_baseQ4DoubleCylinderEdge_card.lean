-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4DoubleCylinderEdge_card
-- name    : QEC.Coding.BDL26TannerLocalRegularity.baseQ4DoubleCylinderEdge_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:33:13.25546+00:00
-- url     : https://prove2.me/theorems/81585822-21e0-4d0c-8adc-e98949eb8eb6
-- title:
--   BDL26 Tanner Local Regularity: base Q4 Double Cylinder Edge card
-- statement:
--   The BDL26 Tanner Local Regularity construction uses the base Q4 Double Cylinder Edge card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3207-L3210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3207-L3210

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

theorem QEC.Coding.BDL26TannerLocalRegularity.baseQ4DoubleCylinderEdge_card :
    Fintype.card (QDoubleCylinderEdge baseTannerSquarePresentation
      (4 : BaseQubit) scaleFive) = 10 := by sorry
