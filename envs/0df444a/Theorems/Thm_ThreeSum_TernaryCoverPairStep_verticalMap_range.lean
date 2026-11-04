-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverPairStep_verticalMap_range
-- name    : ThreeSum.TernaryCoverPairStep.verticalMap_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:20.240835+00:00
-- url     : https://prove2.me/theorems/56afc6d7-d814-47ee-95c6-7c30b6acfc29
-- title:
--   Ternary Cover Pair Step: vertical Map range
-- statement:
--   The Ternary Cover Pair Step construction uses the vertical Map range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPairStep.lean#L39-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPairStep.lean#L39-L54

import Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryCoverPairStep
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverPairStep
open Finset TernaryCoverRankFibers
variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

theorem ThreeSum.TernaryCoverPairStep.verticalMap_range (S : Submodule K (X × (K × K))) :
    LinearMap.range (verticalMap S) = LinearMap.ker (prefixMap S) := by sorry
