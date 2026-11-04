-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceCatalog_Stored_decoded
-- name    : ThreeSum.LightBlockSourceCatalog.Stored.decoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:47:18.166068+00:00
-- url     : https://prove2.me/theorems/ffbc29e4-7a7e-43f7-8006-54f5c3812c79
-- title:
--   Stored: decoded
-- statement:
--   The Stored construction uses the decoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceCatalog.lean#L59-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceCatalog.lean#L59-L66

import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatch
import Definitions.Def_Submission_ThreeSum_LightSourceOccurrenceArray
import Definitions.Def_Submission_ThreeSum_BlockSourceOccurrenceOrder
import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceCatalog
open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding LightBlockSourceBatchLayout
open BlockSourceOccurrenceOrder OutputDecodeOrder OutputDecodeRecords
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

theorem ThreeSum.LightBlockSourceCatalog.Stored.decoded {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {μ : ℕ → ℤ} {h J base cut k : ℕ} {P shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ}
    (H : Stored μ h J base cut P shift B b A a) (hk : k < localCount h^J) :
    LightBlockSourceBatch.BankAt μ base (count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k)
      P shift B b A a ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)) := by sorry
