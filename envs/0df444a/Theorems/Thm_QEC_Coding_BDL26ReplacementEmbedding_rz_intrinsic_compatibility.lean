-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rz_intrinsic_compatibility
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rz_intrinsic_compatibility
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T21:34:12.121374+00:00
-- url     : https://prove2.me/theorems/e5d7fe2a-326d-40f9-892b-e09d09928bbe
-- title:
--   BDL26 Replacement Embedding: rz intrinsic compatibility
-- statement:
--   Dual compatibility preserves the existing intrinsic-zero carrier exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3673-L3676
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3673-L3676

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
open BDL26DecodingGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.rz_intrinsic_compatibility (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (u : Vertex P) (v : RZZeroCell P S u) :
    rzVertexPoint P A S J (rzZeroInclude P A S u v) = rzIntrinsicPoint P S J u v := by sorry
