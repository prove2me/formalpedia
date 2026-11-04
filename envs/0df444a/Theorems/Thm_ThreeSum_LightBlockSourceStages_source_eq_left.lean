-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceStages_source_eq_left
-- name    : ThreeSum.LightBlockSourceStages.source_eq_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:42.553803+00:00
-- url     : https://prove2.me/theorems/f4112bc2-af1e-4011-bbc2-592641363ca4
-- title:
--   Light Block Source Stages: source eq left
-- statement:
--   The Light Block Source Stages construction uses the source eq left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceStages.lean#L21-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceStages.lean#L21-L32

import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
import Definitions.Def_Submission_ThreeSum_BlockSourceTableLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000

theorem ThreeSum.LightBlockSourceStages.source_eq_left {β : Type*} [Fintype β] [DecidableEq β]
    {h J N src : ℕ} (μ : ℕ → ℤ) (p : ℕ) (B : Finset β) (b : β → ℤ)
    (q : GlobalOutput h J) (e : Fin N ≃ B)
    (hinput : ∀ i : Fin N, μ (src+i.val) = b (e i)) :
    LightSourceStages.source μ src N p (modulus h J) 0
      (fun S => endpointLeft (outputOccurrences q) (unindexSet S))
      (fun S => if LeftAllowed (outputOccurrences q) (unindexSet S) then 1 else 0) =
      BlockIndexedQuery.leftSource (p : ℤ) B b q := by sorry
