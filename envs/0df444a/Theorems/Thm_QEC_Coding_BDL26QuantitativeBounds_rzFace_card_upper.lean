-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_rzFace_card_upper
-- name    : QEC.Coding.BDL26QuantitativeBounds.rzFace_card_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:45:06.202472+00:00
-- url     : https://prove2.me/theorems/c8e2b027-2809-4908-a2d1-e2bf54980ae2
-- title:
--   BDL26 Quantitative Bounds: rz Face card upper
-- statement:
--   The BDL26 Quantitative Bounds construction uses the rz Face card upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L371-L375
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L371-L375

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.rzFace_card_upper (P : TannerSquarePresentation) (S : OddScale) :
    Fintype.card (BDL26RZLocalReplacement.RZFace P S) ≤
      faceGrowthFactor S * Fintype.card P.Face := by sorry
