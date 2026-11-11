-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_fineQuadrantImage_diagonal_subset
-- name    : QEC.Coding.BDL26ReplacementEmbedding.fineQuadrantImage_diagonal_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:39:13.495602+00:00
-- url     : https://prove2.me/theorems/bb73c105-a506-473c-b925-83e2e5033d94
-- title:
--   BDL26 Replacement Embedding: fine Quadrant Image diagonal subset
-- statement:
--   Diagonal cells use their actual diagonal triangulation, never the tetrahedral hull.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2384-L2409
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2384-L2409

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

theorem QEC.Coding.BDL26ReplacementEmbedding.fineQuadrantImage_diagonal_subset (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m : ℤ) (a : BDL26FiniteTannerSquare.Two)
    (hm0 : 0 ≤ m) (hm1 : m + 1 ≤ (S.ell : ℤ)) :
    fineQuadrantImage P S J f m m a a ⊆
      oldTriangleImage P J (f, 0) ∪ oldTriangleImage P J (f, 1) := by sorry
