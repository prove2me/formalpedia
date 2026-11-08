-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0DoubleCylinderVertex_card
-- name    : QEC.Coding.BDL26TannerLocalRegularity.baseQ0DoubleCylinderVertex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:34:13.20452+00:00
-- url     : https://prove2.me/theorems/53625e8c-2b0a-404f-9f3f-80af49d0a5bf
-- title:
--   BDL26 Tanner Local Regularity: base Q0 Double Cylinder Vertex card
-- statement:
--   The BDL26 Tanner Local Regularity construction uses the base Q0 Double Cylinder Vertex card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3192-L3195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3192-L3195

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

theorem QEC.Coding.BDL26TannerLocalRegularity.baseQ0DoubleCylinderVertex_card :
    Fintype.card (QDoubleCylinderVertex baseTannerSquarePresentation
      (0 : BaseQubit) scaleFive) = 6 := by sorry
