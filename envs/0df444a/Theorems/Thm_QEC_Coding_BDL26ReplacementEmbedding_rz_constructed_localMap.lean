-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rz_constructed_localMap
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rz_constructed_localMap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T21:34:22.279639+00:00
-- url     : https://prove2.me/theorems/b66f6201-812b-47c6-a926-ee2667aee676
-- title:
--   BDL26 Replacement Embedding: rz constructed local Map
-- statement:
--   The RZ output uses constructed successor admissibility and the actual reversed geometry.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3493-L3510
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3493-L3510

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rz_constructed_localMap (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (J : Vertex P → E)
    {lower width tPrime : ℝ} (hlower : 0 < lower) (hwidth : 0 < width)
    (hgeo : IncomingFaceGeometry P S J lower width)
    (hincoming : ∀ center,
      ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    IsBoundedDensityLocalMap
      (BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzVertexPoint P A4.toTannerSquareAdmissible S J)
      (48 * Real.pi * tPrime * S.ell ^ 2 / (lower * width)) := by sorry
