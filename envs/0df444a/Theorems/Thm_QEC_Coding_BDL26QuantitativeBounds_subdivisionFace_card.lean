-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_subdivisionFace_card
-- name    : QEC.Coding.BDL26QuantitativeBounds.subdivisionFace_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:43:35.038139+00:00
-- url     : https://prove2.me/theorems/d0fb6fad-1a7d-49e3-aea0-f059a4c40606
-- title:
--   BDL26 Quantitative Bounds: subdivision Face card
-- statement:
--   Every old face contributes precisely an m by m grid.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L35-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L35-L39

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.subdivisionFace_card (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Fintype.card (SubdivisionFace P x S) =
      Fintype.card (XStarFace P x) * S.half ^ 2 := by sorry
