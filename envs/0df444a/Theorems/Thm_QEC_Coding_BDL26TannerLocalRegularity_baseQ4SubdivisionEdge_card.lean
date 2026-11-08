-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4SubdivisionEdge_card
-- name    : QEC.Coding.BDL26TannerLocalRegularity.baseQ4SubdivisionEdge_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:32:57.018168+00:00
-- url     : https://prove2.me/theorems/783a2959-b74b-4e2e-b293-2b1e9953a784
-- title:
--   BDL26 Tanner Local Regularity: base Q4 Subdivision Edge card
-- statement:
--   The BDL26 Tanner Local Regularity construction uses the base Q4 Subdivision Edge card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3187-L3190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3187-L3190

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

theorem QEC.Coding.BDL26TannerLocalRegularity.baseQ4SubdivisionEdge_card :
    Fintype.card (QSubdivisionEdge baseTannerSquarePresentation
      (4 : BaseQubit) scaleFive) = 4 := by sorry
