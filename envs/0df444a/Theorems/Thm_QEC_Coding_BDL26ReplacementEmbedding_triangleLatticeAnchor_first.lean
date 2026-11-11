-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangleLatticeAnchor_first
-- name    : QEC.Coding.BDL26ReplacementEmbedding.triangleLatticeAnchor_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:34:26.81703+00:00
-- url     : https://prove2.me/theorems/e46086f7-3e54-441b-a425-cc32dba91525
-- title:
--   BDL26 Replacement Embedding: triangle Lattice Anchor first
-- statement:
--   The BDL26 Replacement Embedding construction uses the triangle Lattice Anchor first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1349-L1358
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1349-L1358

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

theorem QEC.Coding.BDL26ReplacementEmbedding.triangleLatticeAnchor_first (o b c : E) (ell : ℝ) (p : ℤ × ℤ)
    (hb : b ≠ 0) :
    ⟪triangleUnitDirection b, triangleLatticeAnchor o b c ell p - o⟫_ℝ =
      (‖b‖ / ell) * p.1 + (⟪triangleUnitDirection b, c⟫_ℝ / ell) * p.2 := by sorry
