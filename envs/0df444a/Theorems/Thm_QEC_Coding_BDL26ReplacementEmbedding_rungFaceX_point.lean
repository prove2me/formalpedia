-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rungFaceX_point
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rungFaceX_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:32:26.435329+00:00
-- url     : https://prove2.me/theorems/6280afc5-73d0-43b5-8b7f-336f98cba67b
-- title:
--   BDL26 Replacement Embedding: rung Face X point
-- statement:
--   A terminal Q rung's actual X endpoint is the contracted old Z in its X star.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L541-L546
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L541-L546

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rungFaceX_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P) (edge : QStarEdge P a.1.2)
    (copy : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (glueFaceX P S ⟨a, .inr edge, copy⟩) =
      (1 - contractionRatio S) • J (.x a.1.1) + contractionRatio S • J (.z edge.1) := by sorry
