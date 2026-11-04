-- Prove2me | Theorems.Thm_ThreeSum_LightPrimeChain_difference_bound
-- name    : ThreeSum.LightPrimeChain.difference_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:29.487009+00:00
-- url     : https://prove2.me/theorems/fc011921-b21a-4d89-badf-8d711fcf1179
-- title:
--   Light Prime Chain: difference bound
-- statement:
--   The Light Prime Chain construction uses the difference bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeChain.lean#L137-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeChain.lean#L137-L152

import Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeChain
open Light WeightedScore LightPrimeMinimum Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum.LightPrimeChain.difference_bound {nA nB nC U : ℕ} {A B C : ℕ → ℤ}
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    ∀ t ∈ ModuloCounts.triples nA nB nC,
      (ModuloCounts.difference A B C t).natAbs ≤ 3*U := by sorry
