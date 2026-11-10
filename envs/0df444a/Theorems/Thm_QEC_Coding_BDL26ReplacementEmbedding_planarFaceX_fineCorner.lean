-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_planarFaceX_fineCorner
-- name    : QEC.Coding.BDL26ReplacementEmbedding.planarFaceX_fineCorner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:38:36.562489+00:00
-- url     : https://prove2.me/theorems/9cba6ce5-25c6-45eb-9a85-9891a4a93815
-- title:
--   BDL26 Replacement Embedding: planar Face X fine Corner
-- statement:
--   A planar quadrant's X corner is a genuine corner of its assigned fine cell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2063-L2071
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2063-L2071

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

theorem QEC.Coding.BDL26ReplacementEmbedding.planarFaceX_fineCorner (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i j : Fin S.half)
    (copy a b : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (localFaceX P S ⟨x, .inl (copy, f, i, j), a, b⟩) =
      faceFineCorner P S J f.1 (2 * (i.val : ℤ) + a.val) (2 * (j.val : ℤ) + b.val) a b := by sorry
