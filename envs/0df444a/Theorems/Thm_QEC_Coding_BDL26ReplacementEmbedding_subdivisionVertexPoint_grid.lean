-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_subdivisionVertexPoint_grid
-- name    : QEC.Coding.BDL26ReplacementEmbedding.subdivisionVertexPoint_grid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:05:19.007232+00:00
-- url     : https://prove2.me/theorems/27835b1b-d6d8-4035-8349-37a00fe81913
-- title:
--   BDL26 Replacement Embedding: subdivision Vertex Point grid
-- statement:
--   Every materialized grid vertex has the common folded-square position, including
--   all four corners, shared edge tags, and the face-interior tags.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L784-L836
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L784-L836

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
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.subdivisionVertexPoint_grid (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x)
    (i j : Fin (S.half + 1)) :
    subdivisionVertexPoint P S J x (subdivisionGridVertex P x S f i j) =
      facePoint P J f.1 (2 * (i.val : ℝ) / S.ell) (2 * (j.val : ℝ) / S.ell) := by sorry
