-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rounded_density_slack
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rounded_density_slack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:38:12.709528+00:00
-- url     : https://prove2.me/theorems/54cce334-a1f9-4cce-a7bc-8b1709d5d0d6
-- title:
--   BDL26 Replacement Embedding: rounded density slack
-- statement:
--   The conservative factor 48 leaves enough slack for odd rounding once L≥13.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbedding.lean#L179-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbedding.lean#L179-L184

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rounded_density_slack {L ell : ℝ} (hL : 13 ≤ L)
    (hell : 0 ≤ ell) (hround : ell ≤ L + 2) :
    48 * ell ^ 2 ≤ 64 * L ^ 2 := by sorry
