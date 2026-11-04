-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalSurvivors_colored_decomposition
-- name    : ThreeSum.LightOriginalSurvivors.colored_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:04:46.319482+00:00
-- url     : https://prove2.me/theorems/70c2131f-dd52-4585-8608-a69145c4a9e6
-- title:
--   Light Original Survivors: colored decomposition
-- statement:
--   The Light Original Survivors construction uses the colored decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L63-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L63-L80

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_colored_decomposition

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivors
open LightOriginalBucketFilter LightOriginalCollisionCleanup
attribute [local instance] Classical.propDecidable

theorem ThreeSum.LightOriginalSurvivors.colored_decomposition (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (nA nB nC : ℕ) :
    (∃ i < nA, ∃ j < nB, ∃ k < nC, C k = A i + B j) ↔
      LightDeletedTwoSum.Hit (badIndex keysB nB) B A C nC nA (badIndices keysB nB).length 1 ∨
      LightDeletedTwoSum.Hit (badIndex keysC nC) C A B nB nA (badIndices keysC nC).length (-1) ∨
      ∃ i < nA, ∃ j < (indices keysB nB).length, ∃ k < (indices keysC nC).length,
        C (index keysC nC k) = A i + B (index keysB nB j) := by sorry
