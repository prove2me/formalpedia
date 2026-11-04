-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverPairStep_pairedSet_prior
-- name    : ThreeSum.TernaryCoverPairStep.pairedSet_prior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:25.664107+00:00
-- url     : https://prove2.me/theorems/45ed23cb-d407-40e6-a1ac-baac123934f0
-- title:
--   Ternary Cover Pair Step: paired Set prior
-- statement:
--   The Ternary Cover Pair Step construction uses the paired Set prior property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPairStep.lean#L84-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPairStep.lean#L84-L91

import Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryCoverPairStep
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverPairStep
open Finset TernaryCoverRankFibers
variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
variable {E Z ι : Type*} [Fintype E] [Fintype Z] [Fintype ι] [DecidableEq K]

theorem ThreeSum.TernaryCoverPairStep.pairedSet_prior (left right : E → ι → K) (prior : Z → ι → X)
    (S : Submodule K (X × (K × K))) {ze : Z × E}
    (h : ze ∈ pairedSet left right prior S) : ze.1 ∈ priorSet prior S := by sorry
