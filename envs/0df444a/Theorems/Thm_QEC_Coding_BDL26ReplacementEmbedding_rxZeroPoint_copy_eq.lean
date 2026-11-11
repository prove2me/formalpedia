-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxZeroPoint_copy_eq
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rxZeroPoint_copy_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T20:52:07.47428+00:00
-- url     : https://prove2.me/theorems/edf33c5a-76af-4a0c-8db4-34edd925927b
-- title:
--   BDL26 Replacement Embedding: rx Zero Point copy eq
-- statement:
--   Copy tags are retained in the domain even though their positions coincide.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L450-L453
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L450-L453

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rxZeroPoint_copy_eq (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (v : SubdivisionVertex P x S)
    (a b : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J ⟨x, a, v⟩ = rxZeroPoint P S J ⟨x, b, v⟩ := by sorry
