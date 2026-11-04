-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverTupleCount_tupleSet_card_le
-- name    : ThreeSum.TernaryCoverTupleCount.tupleSet_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:46:25.728416+00:00
-- url     : https://prove2.me/theorems/ee94021c-2ca9-4a1c-8c13-f0005efbb3ce
-- title:
--   Ternary Cover Tuple Count: tuple Set card le
-- statement:
--   Every tuple whose actual columns lie in one fixed relation subspace
--   has at most `P^dim(S)` completions.  The projection-fiber cap is the only
--   local graph counting input; it includes all nonzero scalar projections.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTupleCount.lean#L69-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTupleCount.lean#L69-L104

import Definitions.Def_Submission_ThreeSum_TernaryCoverPairStep
import Mathlib.Data.Fin.Tuple.Basic
import Definitions.Def_Submission_ThreeSum_TernaryCoverTupleCount
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverTupleCount
open Finset TernaryCoverRankFibers TernaryCoverPairStep
variable {K E ι : Type*} [Field K] [Fintype E] [Fintype ι] [DecidableEq K]

theorem ThreeSum.TernaryCoverTupleCount.tupleSet_card_le (left right : E → ι → K) (P : ℕ)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hE : Fintype.card E ≤ P ^ 2)
    (hprojection : ∀ β γ : K, (β ≠ 0 ∨ γ ≠ 0) → ∀ q : ι → K,
      (projectionFiber left right β γ q).card ≤ P) :
    ∀ n (S : Submodule K (Fin n → K × K)),
      (tupleSet left right n S).card ≤ P ^ Module.finrank K S := by sorry
