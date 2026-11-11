-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_glueFaceX_point_offset
-- name    : QEC.Coding.BDL26ReplacementEmbedding.glueFaceX_point_offset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:04:54.887316+00:00
-- url     : https://prove2.me/theorems/88cb7b70-d40f-410f-ad67-b56937507d0b
-- title:
--   BDL26 Replacement Embedding: glue Face X point offset
-- statement:
--   The actual glue X and Q1 endpoints differ by the same old X-Q offset.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1074-L1094
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1074-L1094

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

theorem QEC.Coding.BDL26ReplacementEmbedding.glueFaceX_point_offset (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P) (edge : QDoubleCylinderEdge P a.1.2 S)
    (endpoint : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (glueFaceX P S ⟨a, edge, endpoint⟩) =
      (1 - contractionRatio S) • J (.x a.1.1) +
        rxOnePoint P S J (glueFaceQ1 P S ⟨a, edge, endpoint⟩) -
        (1 - contractionRatio S) • J (.q a.1.2) := by sorry
