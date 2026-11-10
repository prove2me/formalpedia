-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_qToXSubdivisionVertexAtRoot_point
-- name    : QEC.Coding.BDL26ReplacementEmbedding.qToXSubdivisionVertexAtRoot_point
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:32:21.198975+00:00
-- url     : https://prove2.me/theorems/ac25c1ad-e998-46ed-b34e-4dc690119ced
-- title:
--   BDL26 Replacement Embedding: q To XSubdivision Vertex At Root point
-- statement:
--   The same-edge Q-to-X map translates every actual Q-path coordinate by one
--   fixed contraction offset, independently of its root witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L999-L1019
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L999-L1019

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

theorem QEC.Coding.BDL26ReplacementEmbedding.qToXSubdivisionVertexAtRoot_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (q : P.Q) (x : P.X) (hxq : P.xq x q = true)
    (root : QStarEdge P q) (v : QSubdivisionVertex P q S) :
    subdivisionVertexPoint P S J x (qToXSubdivisionVertexAtRoot P q x hxq S root v) =
      (1 - contractionRatio S) • J (.x x) + qSubdivisionVertexPoint P S J q v -
        (1 - contractionRatio S) • J (.q q) := by sorry
