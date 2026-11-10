-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_pathStripFaceQ1_linear
-- name    : QEC.Coding.BDL26ReplacementEmbedding.pathStripFaceQ1_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:53:21.60089+00:00
-- url     : https://prove2.me/theorems/cd30636c-a718-4713-8da7-578d7390d76b
-- title:
--   BDL26 Replacement Embedding: path Strip Face Q1 linear
-- statement:
--   Every actual Q-path endpoint has its coarse-grid endpoint parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1866-L1882
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1866-L1882

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

theorem QEC.Coding.BDL26ReplacementEmbedding.pathStripFaceQ1_linear (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (side copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (endpoint : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (rxFaceQ P S (pathStripFace P S f side copy i endpoint) 1) =
      (1 - 2 * ((gridEndpoint i endpoint).val : ℝ) / S.ell) • J (.q (P.faceQ f side)) +
        (2 * ((gridEndpoint i endpoint).val : ℝ) / S.ell) • J (.z (P.faceZ f)) := by sorry
