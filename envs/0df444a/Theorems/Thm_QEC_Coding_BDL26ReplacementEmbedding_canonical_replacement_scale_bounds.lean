-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_canonical_replacement_scale_bounds
-- name    : QEC.Coding.BDL26ReplacementEmbedding.canonical_replacement_scale_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:07:47.74199+00:00
-- url     : https://prove2.me/theorems/f43f1d84-76af-475f-8a96-252d83ef1f28
-- title:
--   BDL26 Replacement Embedding: canonical replacement scale bounds
-- statement:
--   The canonical source scale, rather than a caller-chosen rounded number, has the
--   strict lower bound and exact upper slack used by the replacement theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3019-L3024
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3019-L3024

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

theorem QEC.Coding.BDL26ReplacementEmbedding.canonical_replacement_scale_bounds {alpha lambda : ℝ}
    (hscale : 13 ≤ (2 * alpha + 1) * lambda) :
    let S := leastOddScaleAbove ((2 * alpha + 1) * lambda) (by linarith)
    (2 * alpha + 1) * lambda < (S.ell : ℝ) ∧
      (S.ell : ℝ) ≤ (2 * alpha + 1) * lambda + 2 := by sorry
