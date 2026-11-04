-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceStages_source_eq_right
-- name    : ThreeSum.LightBlockSourceStages.source_eq_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:38.119619+00:00
-- url     : https://prove2.me/theorems/258b9561-0204-4b56-b439-3df51bd9ef7f
-- title:
--   Light Block Source Stages: source eq right
-- statement:
--   The Light Block Source Stages construction uses the source eq right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceStages.lean#L34-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceStages.lean#L34-L45

import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
import Definitions.Def_Submission_ThreeSum_BlockSourceTableLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000

theorem ThreeSum.LightBlockSourceStages.source_eq_right {β : Type*} [Fintype β] [DecidableEq β]
    {h J N src : ℕ} (μ : ℕ → ℤ) (p : ℕ) (shift : ℤ) (C : Finset β) (c : β → ℤ)
    (q : GlobalOutput h J) (e : Fin N ≃ C)
    (hinput : ∀ i : Fin N, μ (src+i.val) = c (e i)) :
    LightSourceStages.source μ src N p (modulus h J) shift
      (fun S => endpointRight (outputOccurrences q) (unindexSet S))
      (fun S => if RightAllowed (outputOccurrences q) (unindexSet S) then 1 else 0) =
      BlockIndexedQuery.rightSource (p : ℤ) shift C c q := by sorry
