-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedBatchInverse_exists_decode
-- name    : ThreeSum.TernaryWantedBatchInverse.exists_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:46.677315+00:00
-- url     : https://prove2.me/theorems/4933ab1f-6a79-4095-91f2-0190fd42ef5c
-- title:
--   Ternary Wanted Batch Inverse: exists decode
-- statement:
--   The Ternary Wanted Batch Inverse construction uses the exists decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchInverse.lean#L7-L16
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchInverse.lean#L7-L16

import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchInverse
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchInverse
open TernaryWantedBatchProvenance

theorem ThreeSum.TernaryWantedBatchInverse.exists_decode (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ→ℤ) (positions : ℕ→ℕ) (n : ℕ) (d : Descriptor)
    (hd : d∈descriptors P J raws targets n) :
    ∃ j : Fin (TernaryWantedBatchIndex.entries P R S J raws words maps targets positions n).length,
      decode P R S J raws words maps targets positions n j=d := by sorry
