-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_leastOddScaleAbove_le_add_two
-- name    : QEC.Coding.BDL26ReplacementEmbedding.leastOddScaleAbove_le_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:41:04.153911+00:00
-- url     : https://prove2.me/theorems/1d1b3c2e-beb8-444f-af55-18fae5795625
-- title:
--   BDL26 Replacement Embedding: least Odd Scale Above le add two
-- statement:
--   The actual least odd scale lies at most two above the real threshold.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3006-L3015
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3006-L3015

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

theorem QEC.Coding.BDL26ReplacementEmbedding.leastOddScaleAbove_le_add_two (threshold : ℝ) (hone : 1 ≤ threshold) :
    ((leastOddScaleAbove threshold hone).ell : ℝ) ≤ threshold + 2 := by sorry
