-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPostABI_host_safe
-- name    : ThreeSum.WeightedGlobalColoredPostABI.host_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:14:54.771905+00:00
-- url     : https://prove2.me/theorems/0d11aabf-c875-4bd5-89c9-a766e110d9bd
-- title:
--   Weighted Global Colored Post ABI: host safe
-- statement:
--   The Weighted Global Colored Post ABI construction uses the host safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L116-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L116-L134

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPostABI
open Light LightWeightedGlobalColoredSolver WeightedGlobalArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000

theorem ThreeSum.WeightedGlobalColoredPostABI.host_safe {lim : Limits} (loc μ : ℕ→ℤ) (host : ℕ)
    (hloc : loc 10=(host : ℤ)) (hspace : host+106≤lim.space)
    (hw : (lim.space : ℤ)≤lim.word) :
    ∀e∈hostArgs,e.Safe lim ⟨loc,μ⟩ := by sorry
