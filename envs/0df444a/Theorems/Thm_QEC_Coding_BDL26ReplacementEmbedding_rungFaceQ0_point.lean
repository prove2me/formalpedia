-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rungFaceQ0_point
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rungFaceQ0_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:32:22.732689+00:00
-- url     : https://prove2.me/theorems/fd7cf40c-cc38-4777-b09d-e50723538fa2
-- title:
--   BDL26 Replacement Embedding: rung Face Q0 point
-- statement:
--   The actual X-local vertical edge collapses to its common endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L549-L557
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L549-L557

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rungFaceQ0_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P) (edge : QStarEdge P a.1.2)
    (copy : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (glueFaceQ0 P S ⟨a, .inr edge, copy⟩) =
      (1 - contractionRatio S) • J (.x a.1.1) + contractionRatio S • J (.z edge.1) := by sorry
