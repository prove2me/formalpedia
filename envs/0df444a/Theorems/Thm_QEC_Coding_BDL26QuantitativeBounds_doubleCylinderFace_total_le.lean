-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_doubleCylinderFace_total_le
-- name    : QEC.Coding.BDL26QuantitativeBounds.doubleCylinderFace_total_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:46:41.256266+00:00
-- url     : https://prove2.me/theorems/92eeaadc-a517-43df-b3a4-ac68dea2da6a
-- title:
--   BDL26 Quantitative Bounds: double Cylinder Face total le
-- statement:
--   The two end-copy face families and boundary rectangles have a uniform
--   finite total bound, before applying the four local corner labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L320-L328
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L320-L328

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.doubleCylinderFace_total_le (P : TannerSquarePresentation) (S : OddScale) :
    (∑ x : P.X, Fintype.card (DoubleCylinderFace P x S)) ≤
      (2 * S.half ^ 2 + 2 * S.half) * Fintype.card P.Face := by sorry
