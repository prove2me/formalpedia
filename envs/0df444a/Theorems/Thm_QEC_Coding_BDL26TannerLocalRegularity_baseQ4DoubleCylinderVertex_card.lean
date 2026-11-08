-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4DoubleCylinderVertex_card
-- name    : QEC.Coding.BDL26TannerLocalRegularity.baseQ4DoubleCylinderVertex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:33:19.607148+00:00
-- url     : https://prove2.me/theorems/243cb47a-2967-45fb-8614-aa531ab5fb96
-- title:
--   BDL26 Tanner Local Regularity: base Q4 Double Cylinder Vertex card
-- statement:
--   The BDL26 Tanner Local Regularity construction uses the base Q4 Double Cylinder Vertex card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3202-L3205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3202-L3205

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

theorem QEC.Coding.BDL26TannerLocalRegularity.baseQ4DoubleCylinderVertex_card :
    Fintype.card (QDoubleCylinderVertex baseTannerSquarePresentation
      (4 : BaseQubit) scaleFive) = 10 := by sorry
