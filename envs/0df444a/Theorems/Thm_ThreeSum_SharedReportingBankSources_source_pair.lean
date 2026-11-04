-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankSources_source_pair
-- name    : ThreeSum.SharedReportingBankSources.source_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:10:08.470979+00:00
-- url     : https://prove2.me/theorems/a8ff9598-8646-4c83-b032-73bf9b2f37e8
-- title:
--   Shared Reporting Bank Sources: source pair
-- statement:
--   The Shared Reporting Bank Sources construction uses the source pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSources.lean#L25-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSources.lean#L25-L39

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light GlobalEncoding BlockEncoding BlockIndexedQuery SharedReportingBankData
open BlockSourceOccurrenceOrder BlockSourceSharing OutputDecodeRecords

theorem ThreeSum.SharedReportingBankSources.source_pair {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {base NB NC g h J cut occ i j s : ℕ} {p shift : ℤ}
    (H : SourceBandBankData.Stored μ fB fC base NB NC g h J cut occ p shift)
    (hi : i < SourceBandPairSlices.count NB NC g) (hj : j < SourceBandPairSlices.count NB NC g)
    (hs : s < LightBlockSourceCatalog.count h J) :
    μ (leftCell base h J cut i s)=(leftBase base h J cut i s : ℤ) ∧
      μ (rightCell base h J cut j s)=(rightBase base h J cut j s : ℤ) ∧
      LightZetaStages.StoredThrough μ (leftBase base h J cut i s) cut
        (leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
          (representative h J s)) (J*(512*h)) ∧
      LightZetaStages.StoredThrough μ (rightBase base h J cut j s) cut
        (rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val)
          (representative h J s)) (J*(512*h)) := by sorry
