-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_faceFineAnchor_lower_lattice
-- name    : QEC.Coding.BDL26ReplacementEmbedding.faceFineAnchor_lower_lattice
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:39:03.969798+00:00
-- url     : https://prove2.me/theorems/7ee35fda-4933-4e54-8ae7-959da2731d1f
-- title:
--   BDL26 Replacement Embedding: face Fine Anchor lower lattice
-- statement:
--   The canonical actual face anchor is exactly the selected lower-chart lattice point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2311-L2321
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2311-L2321

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

theorem QEC.Coding.BDL26ReplacementEmbedding.faceFineAnchor_lower_lattice (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (h : n ≤ m) :
    faceFineAnchor P S J f m n =
      triangleLatticeAnchor (J (.x (P.faceX f)))
        (J (.q (P.faceQ f 0)) - J (.x (P.faceX f)))
        (J (.z (P.faceZ f)) - J (.x (P.faceX f))) S.ell
        (triangleGridIndex 0 (m, n)) := by sorry
