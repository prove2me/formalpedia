-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_pathStrip_boundaryUnit
-- name    : QEC.Coding.BDL26ReplacementEmbedding.pathStrip_boundaryUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:40:32.767013+00:00
-- url     : https://prove2.me/theorems/d2257de7-1f21-4541-8aa5-79d7952681d3
-- title:
--   BDL26 Replacement Embedding: path Strip boundary Unit
-- statement:
--   The final column's actual Q order is exchanged, with the same genuine unit boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3114-L3127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3114-L3127

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

theorem QEC.Coding.BDL26ReplacementEmbedding.pathStrip_boundaryUnit (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) (i : Fin S.half)
    (a : BDL26FiniteTannerSquare.Two) :
    rxFaceBoundaryUnit P S J (pathStripFace P S f 0 copy i a) := by sorry
