-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverPairStep_pair_step_count
-- name    : ThreeSum.TernaryCoverPairStep.pair_step_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:46:20.336567+00:00
-- url     : https://prove2.me/theorems/877ecd7d-fadb-40a6-982c-3f8e0dcc82d6
-- title:
--   Ternary Cover Pair Step: pair step count
-- statement:
--   The Ternary Cover Pair Step construction uses the pair step count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPairStep.lean#L93-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPairStep.lean#L93-L138

import Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryCoverPairStep
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverPairStep
open Finset TernaryCoverRankFibers
variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
variable {E Z ι : Type*} [Fintype E] [Fintype Z] [Fintype ι] [DecidableEq K]

theorem ThreeSum.TernaryCoverPairStep.pair_step_count (left right : E → ι → K) (prior : Z → ι → X) (P : ℕ)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hE : Fintype.card E ≤ P ^ 2)
    (hprojection : ∀ β γ : K, (β ≠ 0 ∨ γ ≠ 0) → ∀ q : ι → K,
      (projectionFiber left right β γ q).card ≤ P)
    (S : Submodule K (X × (K × K))) :
    (pairedSet left right prior S).card ≤
      (priorSet prior S).card * P ^ Module.finrank K (vertical S) := by sorry
