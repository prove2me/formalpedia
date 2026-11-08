-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_int_interval_card_le
-- name    : QEC.Coding.BDL26ReplacementEmbedding.int_interval_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:38:40.64799+00:00
-- url     : https://prove2.me/theorems/13a6a175-6815-411d-aadf-cf6b468b6e42
-- title:
--   BDL26 Replacement Embedding: int interval card le
-- statement:
--   A finite integer set contained in a real interval has the expected endpoint-inclusive count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbedding.lean#L231-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbedding.lean#L231-L255

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open BDL26FiniteTannerSquare
open scoped BigOperators

theorem QEC.Coding.BDL26ReplacementEmbedding.int_interval_card_le (s : Finset ℤ) {a b : ℝ} (hab : a ≤ b)
    (hmem : ∀ z ∈ s, a ≤ (z : ℝ) ∧ (z : ℝ) ≤ b) :
    (s.card : ℝ) ≤ b - a + 1 := by sorry
