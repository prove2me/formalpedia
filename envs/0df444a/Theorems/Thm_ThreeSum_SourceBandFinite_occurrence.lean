-- Prove2me | Theorems.Thm_ThreeSum_SourceBandFinite_occurrence
-- name    : ThreeSum.SourceBandFinite.occurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:15:55.454425+00:00
-- url     : https://prove2.me/theorems/88a3e251-7381-4b70-8416-517b35e2635e
-- title:
--   Source Band Finite: occurrence
-- statement:
--   The Source Band Finite construction uses the occurrence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandFinite.lean#L17-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandFinite.lean#L17-L25

import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandFinite
open GlobalEncoding OutputDecodeRecords

theorem ThreeSum.SourceBandFinite.occurrence {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut occ i k : ℕ} {p shift : ℤ}
    (H : SourceBandBankData.Stored μ fL fR base NL NR g h J cut occ p shift)
    (hi : i < SourceBandPairSlices.count NL NR g) (hk : k < LightBlockSourceCatalog.count h J) :
    LightBlockSourceBatch.BankAt μ (SourceBandBankLayout.baseAt (base+5) h J cut i)
      (LightBlockSourceCatalog.count h J) cut k p shift
      (BandRawA.finiteBandPositions NL g i) (fun t : Fin NL => fL t.val)
      (BandRawA.finiteBandPositions NR g i) (fun t : Fin NR => fR t.val)
      (BlockSourceOccurrenceOrder.representative h J k) := by sorry
