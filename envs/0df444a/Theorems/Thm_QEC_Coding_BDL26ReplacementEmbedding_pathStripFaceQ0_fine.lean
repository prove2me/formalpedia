-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_pathStripFaceQ0_fine
-- name    : QEC.Coding.BDL26ReplacementEmbedding.pathStripFaceQ0_fine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:37:18.736198+00:00
-- url     : https://prove2.me/theorems/d62a8370-2afa-4f37-93f5-4281693b2d8a
-- title:
--   BDL26 Replacement Embedding: path Strip Face Q0 fine
-- statement:
--   The same-edge Q midpoint is the inner edge midpoint of that fine column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1925-L1938
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1925-L1938

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

theorem QEC.Coding.BDL26ReplacementEmbedding.pathStripFaceQ0_fine (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (endpoint : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (rxFaceQ P S (pathStripFace P S f 0 copy i endpoint) 0) =
      facePoint P J f (contractionRatio S) ((2 * (i.val : ℝ) + 1) / S.ell) := by sorry
