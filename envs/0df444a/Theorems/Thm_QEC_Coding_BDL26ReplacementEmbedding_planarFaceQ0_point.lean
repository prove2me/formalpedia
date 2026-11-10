-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_planarFaceQ0_point
-- name    : QEC.Coding.BDL26ReplacementEmbedding.planarFaceQ0_point
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:31:58.945659+00:00
-- url     : https://prove2.me/theorems/597a00f8-a6cd-4b47-a41b-04c5923ba54a
-- title:
--   BDL26 Replacement Embedding: planar Face Q0 point
-- statement:
--   The actual horizontal Q corner lies at the midpoint of its tagged subdivision edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L954-L969
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L954-L969

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

theorem QEC.Coding.BDL26ReplacementEmbedding.planarFaceQ0_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i j : Fin S.half)
    (copy a b : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (localFaceQ0 P S ⟨x, .inl (copy, f, i, j), a, b⟩) =
      facePoint P J f.1 ((2 * (i.val : ℝ) + 1) / S.ell)
        (2 * ((gridEndpoint j b).val : ℝ) / S.ell) := by sorry
