-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxLocalSquare_boundaryUnit
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rxLocalSquare_boundaryUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T21:36:58.652202+00:00
-- url     : https://prove2.me/theorems/9c7125ba-501e-4294-ba8f-ef64feca9177
-- title:
--   BDL26 Replacement Embedding: rx Local Square boundary Unit
-- statement:
--   Local square boundary lengths are inherited through the concrete face inclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3753-L3758
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3753-L3758

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rxLocalSquare_boundaryUnit (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (x : P.X)
    (f : DoubleCylinderFace P x S × (BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two)) :
    rxFaceBoundaryUnit P S J (rxLocalFaceInclude P S x f) := by sorry
