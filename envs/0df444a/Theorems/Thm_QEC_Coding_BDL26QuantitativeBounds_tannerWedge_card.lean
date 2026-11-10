-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_tannerWedge_card
-- name    : QEC.Coding.BDL26QuantitativeBounds.tannerWedge_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:44:37.661101+00:00
-- url     : https://prove2.me/theorems/6da0ea40-c284-4551-b628-63260c1f66c3
-- title:
--   BDL26 Quantitative Bounds: tanner Wedge card
-- statement:
--   The BDL26 Quantitative Bounds construction uses the tanner Wedge card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L202-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L202-L205

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.tannerWedge_card (P : TannerSquarePresentation) :
    Fintype.card (TannerWedge P) = 2 * Fintype.card P.Face := by sorry
