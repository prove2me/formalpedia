-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangleAreaProduct_sq
-- name    : QEC.Coding.BDL26ReplacementEmbedding.triangleAreaProduct_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:36:57.353531+00:00
-- url     : https://prove2.me/theorems/b00442b2-a8a3-4148-87d7-ff8632ee2ac1
-- title:
--   BDL26 Replacement Embedding: triangle Area Product sq
-- statement:
--   The Gram determinant certifies the area product without an orientation choice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1486-L1495
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1486-L1495

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

theorem QEC.Coding.BDL26ReplacementEmbedding.triangleAreaProduct_sq (b c : E) :
    triangleAreaProduct b c ^ 2 = ‖b‖ ^ 2 * ‖c‖ ^ 2 - ⟪b, c⟫_ℝ ^ 2 := by sorry
