-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzFace_boundaryUnit
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rzFace_boundaryUnit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:40:56.0952+00:00
-- url     : https://prove2.me/theorems/b303572e-2a8b-4fce-9ac3-620ee575e1ab
-- title:
--   BDL26 Replacement Embedding: rz Face boundary Unit
-- statement:
--   The concrete RZ boundary uses the actual reversed RX endpoint maps.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3297-L3308
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3297-L3308

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rzFace_boundaryUnit (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) {lower width : ℝ}
    (hgeo : IncomingFaceGeometry P S J lower width)
    (f : BDL26RZLocalReplacement.RZFace P S) :
    BoundaryUnit (rzXPoint P S J (BDL26RZLocalReplacement.rzFaceX P S f))
      (rzQPoint P S J (BDL26RZLocalReplacement.rzFaceQ P A S f 0))
      (rzQPoint P S J (BDL26RZLocalReplacement.rzFaceQ P A S f 1))
      (rzZPoint P S J (BDL26RZLocalReplacement.rzFaceZ P A S f)) := by sorry
