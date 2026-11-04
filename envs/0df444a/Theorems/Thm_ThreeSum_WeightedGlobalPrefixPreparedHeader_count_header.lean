-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrefixPreparedHeader_count_header
-- name    : ThreeSum.WeightedGlobalPrefixPreparedHeader.count_header
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:56:27.487872+00:00
-- url     : https://prove2.me/theorems/0e19a07a-a33e-448c-bef5-87cf648c859f
-- title:
--   Weighted Global Prefix Prepared Header: count header
-- statement:
--   The actual count write performed by SeedScore yields the exact host ABI;
--   no configuration header is supplied as advice to the machine.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixPreparedHeader.lean#L59-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixPreparedHeader.lean#L59-L67

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaHeaderAgreement
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixPrepare
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixPreparedHeader
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrefixPreparedHeader
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaHeaderAgreement
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalPrefixPreparedHeader.count_header {ν : ℕ→ℤ} (I : Input) (j : ℕ)
    (maps : Fin F→WeightedGlobalCoverGoodMaps.Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (ret : ℤ)
    (hs : Seg ν (addr I.free I.capacity 1) (emittedHeader I p m F j Q ret)) :
    Seg (Function.update ν (addr I.free I.capacity 1+104)
      ((entries (r:=j+1) maps τ I).length:ℤ)) (addr I.free I.capacity 1)
      (setup (r:=j+1) maps τ cap Q I).argv := by sorry
