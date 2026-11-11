-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangle_lattice_card_le
-- name    : QEC.Coding.BDL26ReplacementEmbedding.triangle_lattice_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:33:55.66003+00:00
-- url     : https://prove2.me/theorems/69ebf6a3-ce7c-4252-bb47-29d22c190f5d
-- title:
--   BDL26 Replacement Embedding: triangle lattice card le
-- statement:
--   Packing is derived in the actual constructed triangle frame, with no frame
--   or point-count certificate supplied by the caller.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1383-L1402
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1383-L1402

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

theorem QEC.Coding.BDL26ReplacementEmbedding.triangle_lattice_card_le (s : Finset (ℤ × ℤ)) (o b c z : E) {ell : ℝ}
    (hell : 0 < ell) (hb : b ≠ 0) (hc : triangleAltitudeVector b c ≠ 0)
    (hbL : ‖b‖ ≤ ell) (hcL : ‖c‖ ≤ ell)
    (hmem : ∀ p ∈ s, dist (triangleLatticeAnchor o b c ell p) z ≤ 2) :
    (s.card : ℝ) ≤ 8 * Real.pi * ell ^ 2 / (‖b‖ * ‖triangleAltitudeVector b c‖) := by sorry
