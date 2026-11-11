-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_fineQuadrantImage_subset_lower
-- name    : QEC.Coding.BDL26ReplacementEmbedding.fineQuadrantImage_subset_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:39:31.86564+00:00
-- url     : https://prove2.me/theorems/f88d2c0e-81ca-43dc-855a-4bd58c336946
-- title:
--   BDL26 Replacement Embedding: fine Quadrant Image subset lower
-- statement:
--   A fine cell strictly below the fold stays in the actual old lower triangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2358-L2368
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2358-L2368

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

theorem QEC.Coding.BDL26ReplacementEmbedding.fineQuadrantImage_subset_lower (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (hm : m + 1 ≤ (S.ell : ℤ)) (hn : 0 ≤ n) (hnm : n + 1 ≤ m) :
    fineQuadrantImage P S J f m n a b ⊆ oldTriangleImage P J (f, 0) := by sorry
