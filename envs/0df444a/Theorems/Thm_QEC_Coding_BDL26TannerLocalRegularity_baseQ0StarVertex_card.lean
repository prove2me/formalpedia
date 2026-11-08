-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0StarVertex_card
-- name    : QEC.Coding.BDL26TannerLocalRegularity.baseQ0StarVertex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:32:07.458916+00:00
-- url     : https://prove2.me/theorems/42690c97-d2c7-4bce-a618-f1f6e53694a1
-- title:
--   BDL26 Tanner Local Regularity: base Q0 Star Vertex card
-- statement:
--   The BDL26 Tanner Local Regularity construction uses the base Q0 Star Vertex card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3156-L3158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3156-L3158

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

theorem QEC.Coding.BDL26TannerLocalRegularity.baseQ0StarVertex_card :
    Fintype.card (QStarVertex baseTannerSquarePresentation (0 : BaseQubit)) = 2 := by sorry
