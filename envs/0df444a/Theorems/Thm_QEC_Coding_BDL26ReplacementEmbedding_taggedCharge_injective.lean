-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_taggedCharge_injective
-- name    : QEC.Coding.BDL26ReplacementEmbedding.taggedCharge_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T13:38:21.438534+00:00
-- url     : https://prove2.me/theorems/2a2550f4-5a4b-4891-9067-0edf239ef83f
-- title:
--   BDL26 Replacement Embedding: tagged Charge injective
-- statement:
--   Each positive cell receives at most one label from each family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbedding.lean#L58-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbedding.lean#L58-L73

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

theorem QEC.Coding.BDL26ReplacementEmbedding.taggedCharge_injective (S : OddScale) :
    Function.Injective (fun c : FlatCell S => (chargeTag S c, charge S c)) := by sorry
