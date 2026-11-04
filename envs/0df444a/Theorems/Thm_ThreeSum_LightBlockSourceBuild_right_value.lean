-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceBuild_right_value
-- name    : ThreeSum.LightBlockSourceBuild.right_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:28.780404+00:00
-- url     : https://prove2.me/theorems/fd27cdeb-ad87-4989-82a6-712f62260310
-- title:
--   Light Block Source Build: right value
-- statement:
--   The Light Block Source Build construction uses the right value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBuild.lean#L56-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBuild.lean#L56-L67

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBuild
open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds
set_option maxHeartbeats 1500000

theorem ThreeSum.LightBlockSourceBuild.right_value {β : Type*} [DecidableEq β] {h J N : ℕ}
    (o : Occurrences h J) (p : ℕ) (shift : ℤ) (C : Finset β) (c : β → ℤ)
    (sets : ℕ → Finset (BlockRows.Coord J (512*h))) (values : ℕ → ℤ)
    (e : Fin N ≃ C) (hvalues : ∀ i : Fin N, values i.val = c (e i)) (i : ℕ) :
    LightSourceGather.value (modulus h J) (fun i => endpointRight o (sets i))
      (fun i => if RightAllowed o (sets i) then 1 else 0)
      (fun r => LightHistogram.count
        (fun j => LightSourceResidues.key p (modulus h J) shift (values j)) r N) i =
      rightWeights o (p : ℤ) shift C c (sets i) := by sorry
