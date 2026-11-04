-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverPairStep_prefixMap_range
-- name    : ThreeSum.TernaryCoverPairStep.prefixMap_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:20.56297+00:00
-- url     : https://prove2.me/theorems/888e51f6-abc2-4b2f-b5c9-830a9ad8c73e
-- title:
--   Ternary Cover Pair Step: prefix Map range
-- statement:
--   The Ternary Cover Pair Step construction uses the prefix Map range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPairStep.lean#L56-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPairStep.lean#L56-L63

import Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryCoverPairStep
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverPairStep
open Finset TernaryCoverRankFibers
variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

theorem ThreeSum.TernaryCoverPairStep.prefixMap_range (S : Submodule K (X × (K × K))) :
    LinearMap.range (prefixMap S) = prefixSpace S := by sorry
