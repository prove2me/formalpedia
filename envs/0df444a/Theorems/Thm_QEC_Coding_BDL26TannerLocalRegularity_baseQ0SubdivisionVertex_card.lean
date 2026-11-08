-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0SubdivisionVertex_card
-- name    : QEC.Coding.BDL26TannerLocalRegularity.baseQ0SubdivisionVertex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:32:27.581463+00:00
-- url     : https://prove2.me/theorems/82ec0b38-bc07-44f0-bc22-dc5e426c3f99
-- title:
--   BDL26 Tanner Local Regularity: base Q0 Subdivision Vertex card
-- statement:
--   The BDL26 Tanner Local Regularity construction uses the base Q0 Subdivision Vertex card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3172-L3175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3172-L3175

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

theorem QEC.Coding.BDL26TannerLocalRegularity.baseQ0SubdivisionVertex_card :
    Fintype.card (QSubdivisionVertex baseTannerSquarePresentation
      (0 : BaseQubit) scaleFive) = 3 := by sorry
