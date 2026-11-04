-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverPairStep_verticalMap_injective
-- name    : ThreeSum.TernaryCoverPairStep.verticalMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:14.430906+00:00
-- url     : https://prove2.me/theorems/fa2785c0-73f8-49c4-8458-5cee0c3f23d4
-- title:
--   Ternary Cover Pair Step: vertical Map injective
-- statement:
--   The Ternary Cover Pair Step construction uses the vertical Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPairStep.lean#L33-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPairStep.lean#L33-L37

import Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryCoverPairStep
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverPairStep
open Finset TernaryCoverRankFibers
variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

theorem ThreeSum.TernaryCoverPairStep.verticalMap_injective (S : Submodule K (X × (K × K))) :
    Function.Injective (verticalMap S) := by sorry
