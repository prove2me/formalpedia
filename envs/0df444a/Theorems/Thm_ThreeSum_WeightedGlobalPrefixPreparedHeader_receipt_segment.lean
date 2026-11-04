-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrefixPreparedHeader_receipt_segment
-- name    : ThreeSum.WeightedGlobalPrefixPreparedHeader.receipt_segment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:02:46.222041+00:00
-- url     : https://prove2.me/theorems/4c9fcec3-506a-4761-a105-56a5faeab5c7
-- title:
--   Weighted Global Prefix Prepared Header: receipt segment
-- statement:
--   The Weighted Global Prefix Prepared Header construction uses the receipt segment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixPreparedHeader.lean#L22-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixPreparedHeader.lean#L22-L38

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaHeaderAgreement
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixPrepare
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixPreparedHeader
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrefixPreparedHeader
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaHeaderAgreement
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalPrefixPreparedHeader.receipt_segment {μ ν : ℕ→ℤ} (I : Input) (j J : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (hTemplate : Seg μ (addr I.free I.capacity 0) (templateValues I p m F))
    (H : LightWeightedGlobalPrefixPrepare.HeaderReceipt μ ν m F p
      (addr I.free I.capacity 0) (addr I.free I.capacity 1) I.prefixFree
      (WeightedGlobalLocalParameters.fixedAlpha m 2) (alphaRank m)
      (TernaryCodeSemantics.address Q.val) (4^(WeightedGlobalLocalParameters.fixedLength m)) J j
      (p^j) (addr I.free I.capacity 50) (addr I.free I.capacity 51)) :
    ∃ret, Seg ν (addr I.free I.capacity 1) (emittedHeader I p m F j Q ret) := by sorry
