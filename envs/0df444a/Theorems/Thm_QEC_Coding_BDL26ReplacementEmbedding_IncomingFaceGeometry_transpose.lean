-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_IncomingFaceGeometry_transpose
-- name    : QEC.Coding.BDL26ReplacementEmbedding.IncomingFaceGeometry.transpose
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:07:12.157199+00:00
-- url     : https://prove2.me/theorems/efc7c39f-d48a-474c-abbf-cf6c40ec8921
-- title:
--   Incoming Face Geometry: transpose
-- statement:
--   All old source-side and width hypotheses transport under the actual transpose.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2880-L2918
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2880-L2918

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

theorem QEC.Coding.BDL26ReplacementEmbedding.IncomingFaceGeometry.transpose (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (h : IncomingFaceGeometry P S J lower width) :
    IncomingFaceGeometry (transposePresentation P) S (transposePointMap P J) lower width := by sorry
