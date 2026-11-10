-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_faceFineCorner_mem_upper
-- name    : QEC.Coding.BDL26ReplacementEmbedding.faceFineCorner_mem_upper
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:39:28.442476+00:00
-- url     : https://prove2.me/theorems/f73d8af7-de7f-4481-b57c-3d30759ec7f8
-- title:
--   BDL26 Replacement Embedding: face Fine Corner mem upper
-- statement:
--   The upper chart uses the second actual incoming triangle, including its diagonal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2142-L2163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2142-L2163

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

theorem QEC.Coding.BDL26ReplacementEmbedding.faceFineCorner_mem_upper (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (hv : n + b.val ≤ (S.ell : ℤ)) (hu : 0 ≤ m + a.val)
    (huv : m + a.val ≤ n + b.val) :
    faceFineCorner P S J f m n a b ∈ oldTriangleImage P J (f, 1) := by sorry
