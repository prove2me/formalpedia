-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_glueFaceQ0_point_offset
-- name    : QEC.Coding.BDL26ReplacementEmbedding.glueFaceQ0_point_offset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:35:51.391494+00:00
-- url     : https://prove2.me/theorems/e86f3b5d-a20f-48a0-be53-31bda30a9716
-- title:
--   BDL26 Replacement Embedding: glue Face Q0 point offset
-- statement:
--   The actual glue midpoint pair has that identical geometric offset.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1097-L1110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1097-L1110

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

theorem QEC.Coding.BDL26ReplacementEmbedding.glueFaceQ0_point_offset (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P) (edge : QDoubleCylinderEdge P a.1.2 S)
    (endpoint : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (glueFaceQ0 P S ⟨a, edge, endpoint⟩) =
      (1 - contractionRatio S) • J (.x a.1.1) +
        rxTwoPoint P S J (glueFaceZ P S ⟨a, edge, endpoint⟩) -
        (1 - contractionRatio S) • J (.q a.1.2) := by sorry
