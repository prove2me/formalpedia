-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_fineQuadrantImage_subset_upper
-- name    : QEC.Coding.BDL26ReplacementEmbedding.fineQuadrantImage_subset_upper
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:39:27.368079+00:00
-- url     : https://prove2.me/theorems/b2dc26f1-a626-4a10-97bb-703ee28b56e4
-- title:
--   BDL26 Replacement Embedding: fine Quadrant Image subset upper
-- statement:
--   A fine cell strictly above the fold stays in the actual old upper triangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2371-L2381
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2371-L2381

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

theorem QEC.Coding.BDL26ReplacementEmbedding.fineQuadrantImage_subset_upper (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (hn : n + 1 ≤ (S.ell : ℤ)) (hm : 0 ≤ m) (hmn : m + 1 ≤ n) :
    fineQuadrantImage P S J f m n a b ⊆ oldTriangleImage P J (f, 1) := by sorry
