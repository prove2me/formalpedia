-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_faceFineCorner_mem_lower
-- name    : QEC.Coding.BDL26ReplacementEmbedding.faceFineCorner_mem_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:39:21.7792+00:00
-- url     : https://prove2.me/theorems/a403ca9d-7d06-4e31-89eb-d34f10ffa12a
-- title:
--   BDL26 Replacement Embedding: face Fine Corner mem lower
-- statement:
--   Integer parameter inequalities put a genuine fine corner in the old lower triangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2129-L2139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2129-L2139

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
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.faceFineCorner_mem_lower (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (hu : m + a.val ≤ (S.ell : ℤ)) (hv : 0 ≤ n + b.val)
    (hvu : n + b.val ≤ m + a.val) :
    faceFineCorner P S J f m n a b ∈ oldTriangleImage P J (f, 0) := by sorry
