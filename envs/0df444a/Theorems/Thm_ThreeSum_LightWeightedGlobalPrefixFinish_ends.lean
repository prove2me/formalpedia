-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixFinish_ends
-- name    : ThreeSum.LightWeightedGlobalPrefixFinish.ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:51:44.200998+00:00
-- url     : https://prove2.me/theorems/f2ac7139-9580-4802-abba-1f6e536c86d0
-- title:
--   Light Weighted Global Prefix Finish: ends
-- statement:
--   Actual controller, actual key commits, and actual span commit. All
--   requirements are pure memory/layout certificates.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixFinish.lean#L119-L220
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixFinish.lean#L119-L220

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFullController
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixProgramLibrary
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixFinish
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
import Definitions.Def_WeightedCache3SUM_Alias_2355ab610500aa6c
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_ReportingHostRelocation_ends
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPrefixFinish
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPrefixFinish.ends {C : Config} [Fact C.p.Prime] {D : Family C} {lim : Limits}
    {depth K R S n U dB dC dP tB tC tP newSpan seedTime seed rows : ℕ}
    {raws : List ℤ} {words maps : List ℕ} (l : List ℤ) (μ : ℕ→ℤ)
    (H : FullPlan C D lim (depth+1) K R S n U dB dC dP tB tC tP newSpan seedTime raws words maps μ)
    (A : Layout C lim seed rows newSpan)
    (hseed : l.getD 3 0=(seed:ℤ)) (hJ : l.getD 11 0=(C.J:ℤ)) (hrows : l.getD 19 0=(rows:ℤ))
    (hheader : Seg μ seed (header C n dB dC dP tB tC tP newSpan))
    (hfinal : ∀ν,H.finalState ν→Seg ν seed (header C n dB dC dP tB tC tP newSpan)) :
    Ends lim (program C.p R S K raws words maps D.xl D.yl D.zl D.xr D.yr D.zr) depth body
      ⟨frame l,μ⟩ (time C n seedTime rows)
      (fun σ=>σ.loc 0=(rows:ℤ) ∧ ∃ξ,H.finalState ξ ∧ Committed C rows newSpan ξ σ.mem ∧
        Seg σ.mem seed (header C n dB dC dP tB tC tP newSpan)) := by sorry
