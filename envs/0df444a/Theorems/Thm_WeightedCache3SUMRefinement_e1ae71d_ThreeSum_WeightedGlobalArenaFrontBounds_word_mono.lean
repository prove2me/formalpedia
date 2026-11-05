-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontBounds_word_mono
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFrontBounds.word_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:33:18.702028+00:00
-- url     : https://prove2.me/theorems/6979c101-04b0-4887-a491-97c75425e8ab
-- title:
--   word_mono
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaFrontBounds.lean#L32-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaFrontBounds.lean#L32-L38

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCountReady
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFrontBounds
import Theorems.Thm_ThreeSum_LightExtensionFactorPredicate_word_mono
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_word_mono
import Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_word_mono
import Theorems.Thm_ThreeSum_LightRadixKeys_word_mono
import Theorems.Thm_ThreeSum_ModuloRuntime_word_mono

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFrontBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFrontBounds.word_mono {N nb nb' G count count' R R' V V' : ℕ}
    (hb : nb≤nb') (hc : count≤count') (hr : R≤R') (hv : V≤V') :
    WeightedGlobalFrontendResources.word N nb G count R V≤
      WeightedGlobalFrontendResources.word N nb' G count' R' V' := by sorry
