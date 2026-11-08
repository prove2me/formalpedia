-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0StarEdge_card
-- name    : QEC.Coding.BDL26TannerLocalRegularity.baseQ0StarEdge_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:32:32.590014+00:00
-- url     : https://prove2.me/theorems/6479632a-e2f3-4107-b137-0036d753c9e0
-- title:
--   BDL26 Tanner Local Regularity: base Q0 Star Edge card
-- statement:
--   The BDL26 Tanner Local Regularity construction uses the base Q0 Star Edge card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3160-L3162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3160-L3162

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

theorem QEC.Coding.BDL26TannerLocalRegularity.baseQ0StarEdge_card :
    Fintype.card (QStarEdge baseTannerSquarePresentation (0 : BaseQubit)) = 1 := by sorry
