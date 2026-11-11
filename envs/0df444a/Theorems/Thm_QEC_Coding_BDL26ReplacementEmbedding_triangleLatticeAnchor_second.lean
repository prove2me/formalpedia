-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangleLatticeAnchor_second
-- name    : QEC.Coding.BDL26ReplacementEmbedding.triangleLatticeAnchor_second
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:34:25.345333+00:00
-- url     : https://prove2.me/theorems/e157afb1-70b7-4986-bf41-f882c0f47834
-- title:
--   BDL26 Replacement Embedding: triangle Lattice Anchor second
-- statement:
--   The BDL26 Replacement Embedding construction uses the triangle Lattice Anchor second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1360-L1370
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1360-L1370

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

theorem QEC.Coding.BDL26ReplacementEmbedding.triangleLatticeAnchor_second (o b c : E) (ell : ℝ) (p : ℤ × ℤ)
    (hb : b ≠ 0) (hc : triangleAltitudeVector b c ≠ 0) :
    ⟪triangleUnitDirection (triangleAltitudeVector b c),
      triangleLatticeAnchor o b c ell p - o⟫_ℝ =
      (‖triangleAltitudeVector b c‖ / ell) * p.2 := by sorry
