-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPairMass_pairMass_le
-- name    : ThreeSum.WeightedGlobalArenaPairMass.pairMass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:01:02.196462+00:00
-- url     : https://prove2.me/theorems/2618beae-0d92-4316-ba3f-3aadb717836f
-- title:
--   Weighted Global Arena Pair Mass: pair Mass le
-- statement:
--   The Weighted Global Arena Pair Mass construction uses the pair Mass le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairMass.lean#L41-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairMass.lean#L41-L72

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Definitions.Def_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPairMass
open WeightedGlobalArenaSourceSetup TernaryCanonicalDictionaries WeightedGlobalNativeMomentBounds
open WeightedGlobalNativeCompleteFrontend
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters StageBounds
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaPairMass.pairMass_le (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (M n : ℕ)
    (hM : 1<M) (hr : r≤Nat.clog M (n^2)) (hl : I.nB≤n) (hc : I.nC≤n) :
    pairBound (setup (r := r) maps τ cap Q I)*2^(N m r)≤envelope maps cap M n := by sorry
