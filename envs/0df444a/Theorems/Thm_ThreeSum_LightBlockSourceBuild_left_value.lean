-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceBuild_left_value
-- name    : ThreeSum.LightBlockSourceBuild.left_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:53:24.511635+00:00
-- url     : https://prove2.me/theorems/0e80f9e7-f828-4c3d-88c0-792298e3623b
-- title:
--   Light Block Source Build: left value
-- statement:
--   The Light Block Source Build construction uses the left value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBuild.lean#L43-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBuild.lean#L43-L54

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBuild
open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds
set_option maxHeartbeats 1500000

theorem ThreeSum.LightBlockSourceBuild.left_value {β : Type*} [DecidableEq β] {h J N : ℕ}
    (o : Occurrences h J) (p : ℕ) (B : Finset β) (b : β → ℤ)
    (sets : ℕ → Finset (BlockRows.Coord J (512*h))) (values : ℕ → ℤ)
    (e : Fin N ≃ B) (hvalues : ∀ i : Fin N, values i.val = b (e i)) (i : ℕ) :
    LightSourceGather.value (modulus h J) (fun i => endpointLeft o (sets i))
      (fun i => if LeftAllowed o (sets i) then 1 else 0)
      (fun r => LightHistogram.count
        (fun j => LightSourceResidues.key p (modulus h J) 0 (values j)) r N) i =
      leftWeights o (p : ℤ) B b (sets i) := by sorry
