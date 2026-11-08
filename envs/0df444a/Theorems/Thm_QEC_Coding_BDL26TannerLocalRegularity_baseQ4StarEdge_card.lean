-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4StarEdge_card
-- name    : QEC.Coding.BDL26TannerLocalRegularity.baseQ4StarEdge_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:32:41.822365+00:00
-- url     : https://prove2.me/theorems/e7d3ead7-0ba8-4d6f-b3b0-da2b385ee652
-- title:
--   BDL26 Tanner Local Regularity: base Q4 Star Edge card
-- statement:
--   The BDL26 Tanner Local Regularity construction uses the base Q4 Star Edge card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3168-L3170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3168-L3170

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

theorem QEC.Coding.BDL26TannerLocalRegularity.baseQ4StarEdge_card :
    Fintype.card (QStarEdge baseTannerSquarePresentation (4 : BaseQubit)) = 2 := by sorry
