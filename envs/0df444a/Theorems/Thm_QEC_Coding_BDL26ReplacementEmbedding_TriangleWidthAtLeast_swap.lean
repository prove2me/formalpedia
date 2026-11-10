-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_TriangleWidthAtLeast_swap
-- name    : QEC.Coding.BDL26ReplacementEmbedding.TriangleWidthAtLeast.swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:07:18.244836+00:00
-- url     : https://prove2.me/theorems/d8e06e8d-b16e-49eb-9de8-fd783c4ec243
-- title:
--   Triangle Width At Least: swap
-- statement:
--   Source segment width is independent of the order of the two non-origin vertices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2184-L2190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2184-L2190

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.TriangleWidthAtLeast.swap {b c : E} {delta : ℝ}
    (h : TriangleWidthAtLeast b c delta) : TriangleWidthAtLeast c b delta := by sorry
