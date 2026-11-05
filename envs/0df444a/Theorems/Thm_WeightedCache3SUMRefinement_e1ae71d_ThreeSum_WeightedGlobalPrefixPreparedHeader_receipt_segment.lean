-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrefixPreparedHeader_receipt_segment
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixPreparedHeader.receipt_segment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:04:51.29261+00:00
-- url     : https://prove2.me/theorems/c2c00177-5e97-40f6-822d-26c34ff21e6c
-- title:
--   receipt_segment
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixPreparedHeader.lean#L22-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixPreparedHeader.lean#L22-L38

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaHeaderAgreement
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixPrepare
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixPreparedHeader
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixPreparedHeader
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaHeaderAgreement
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixPreparedHeader.receipt_segment {μ ν : ℕ→ℤ} (I : Input) (j J : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (hTemplate : Seg μ (addr I.free I.capacity 0) (templateValues I p m F))
    (H : LightWeightedGlobalPrefixPrepare.HeaderReceipt μ ν m F p
      (addr I.free I.capacity 0) (addr I.free I.capacity 1) I.prefixFree
      (WeightedGlobalLocalParameters.fixedAlpha m 2) (alphaRank m)
      (TernaryCodeSemantics.address Q.val) (4^(WeightedGlobalLocalParameters.fixedLength m)) J j
      (p^j) (addr I.free I.capacity 50) (addr I.free I.capacity 51)) :
    ∃ret, Seg ν (addr I.free I.capacity 1) (emittedHeader I p m F j Q ret) := by sorry
