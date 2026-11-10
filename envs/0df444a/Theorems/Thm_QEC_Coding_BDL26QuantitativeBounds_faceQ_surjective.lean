-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_faceQ_surjective
-- name    : QEC.Coding.BDL26QuantitativeBounds.faceQ_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:25:59.575366+00:00
-- url     : https://prove2.me/theorems/bc214106-bda2-4e91-9671-3365ebe8675f
-- title:
--   BDL26 Quantitative Bounds: face Q surjective
-- statement:
--   Admissibility ensures every Q coordinate occurs as a face corner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L157-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L157-L164

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.faceQ_surjective (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) :
    Function.Surjective (fun fi : P.Face × BDL26FiniteTannerSquare.Two => P.faceQ fi.1 fi.2) := by sorry
