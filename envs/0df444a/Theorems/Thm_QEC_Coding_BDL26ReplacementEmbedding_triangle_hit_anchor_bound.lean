-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangle_hit_anchor_bound
-- name    : QEC.Coding.BDL26ReplacementEmbedding.triangle_hit_anchor_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:35:39.668338+00:00
-- url     : https://prove2.me/theorems/cecc261d-b034-4545-bb82-3721e55a35bc
-- title:
--   BDL26 Replacement Embedding: triangle hit anchor bound
-- statement:
--   A genuine face-triangle hit transfers to its actual nearby anchor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1446-L1459
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1446-L1459

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

theorem QEC.Coding.BDL26ReplacementEmbedding.triangle_hit_anchor_bound (anchor p q r center : E)
    (hp : dist p anchor ≤ 1) (hq : dist q anchor ≤ 1) (hr : dist r anchor ≤ 1)
    (hhit : (convexHull ℝ {p, q, r} ∩ Metric.closedBall center 1).Nonempty) :
    dist anchor center ≤ 2 := by sorry
