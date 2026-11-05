-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceBounds_bank_size
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds.bank_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:27:14.526894+00:00
-- url     : https://prove2.me/theorems/caad7c4a-0eb7-4c42-883a-31e71dfac39e
-- title:
--   bank_size
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L155-L163
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L155-L163

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceBounds
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
variable {p m F r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds.bank_size (m j : ℕ) : nb m j≤(4^fixedLength m)^j := by sorry
