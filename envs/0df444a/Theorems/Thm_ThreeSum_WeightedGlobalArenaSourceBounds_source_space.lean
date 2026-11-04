-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceBounds_source_space
-- name    : ThreeSum.WeightedGlobalArenaSourceBounds.source_space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:02:58.207628+00:00
-- url     : https://prove2.me/theorems/e1a20835-1ce2-4a98-aad3-06988f7e68dd
-- title:
--   Weighted Global Arena Source Bounds: source space
-- statement:
--   The Weighted Global Arena Source Bounds construction uses the source space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L70-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L70-L93

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSourceBounds.source_space (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    (right : Bool) (n : ℕ) (hnB : I.nB≤n) (hnC : I.nC≤n) :
    LightRadixKeys.space 0 (source (r := r) maps cap I right).xs.length r≤
      (r+1)*((sourceWidth maps cap)^r+1) ∧
    count (source (r := r) maps cap I right).xs p r (p^r)
      (source (r := r) maps cap I right).NL (source (r := r) maps cap I right).input≤
        n*(sourceWidth maps cap)^r ∧
    LightWantedSetup.space 0 (p^r) (source (r := r) maps cap I right).input
      (dictionary (source (r := r) maps cap I right).xs p r)
      (source (r := r) maps cap I right).NL
      (size (source (r := r) maps cap I right).xs r) (p*(p+1)^r) 0 0≤
        10+n+2*(sourceWidth maps cap)^r+4*p^r+p*(p+1)^r+2*n*(sourceWidth maps cap)^r := by sorry
