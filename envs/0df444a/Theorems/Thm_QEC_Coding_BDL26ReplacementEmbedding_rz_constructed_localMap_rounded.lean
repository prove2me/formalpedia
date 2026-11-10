-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rz_constructed_localMap_rounded
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rz_constructed_localMap_rounded
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:43:57.208145+00:00
-- url     : https://prove2.me/theorems/a0e9d23b-25f1-4af8-8f4e-47346753f197
-- title:
--   BDL26 Replacement Embedding: rz constructed local Map rounded
-- statement:
--   The dual placement has the same constant and actual successor incidences.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3537-L3555
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3537-L3555

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.rz_constructed_localMap_rounded (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (J : Vertex P → E) {alpha alpha2 gamma lambda tPrime : ℝ}
    (hlambda : 0 < lambda) (hgamma : 0 < gamma) (halpha2 : 1 < alpha2)
    (htPrime : 0 ≤ tPrime) (hscale : 13 ≤ (2 * alpha + 1) * lambda)
    (hround : (S.ell : ℝ) ≤ (2 * alpha + 1) * lambda + 2)
    (hgeo : IncomingFaceGeometry P S J ((alpha2 - 1) * lambda) (gamma * lambda))
    (hincoming : ∀ center,
      ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    IsBoundedDensityLocalMap
      (BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzVertexPoint P A4.toTannerSquareAdmissible S J)
      (64 * Real.pi * tPrime * (2 * alpha + 1) ^ 2 / (gamma * (alpha2 - 1))) := by sorry
