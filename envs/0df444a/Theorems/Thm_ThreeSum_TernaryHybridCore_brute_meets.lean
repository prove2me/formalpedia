-- Prove2me | Theorems.Thm_ThreeSum_TernaryHybridCore_brute_meets
-- name    : ThreeSum.TernaryHybridCore.brute_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:40:21.976634+00:00
-- url     : https://prove2.me/theorems/5221a3d4-d375-49b7-b7fe-1c7de504b840
-- title:
--   Ternary Hybrid Core: brute meets
-- statement:
--   The Ternary Hybrid Core construction uses the brute meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCore.lean#L66-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCore.lean#L66-L76

import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_TernaryHybridCore
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridCore
open Light
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

theorem ThreeSum.TernaryHybridCore.brute_meets {lim : Limits} {fastP : Program} {fastProc κ cutoff src n U free d : ℕ}
    (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hn : 0<n) (hsrc : src+n≤free) (H : (LightBruteThreeSum.need n U).Ok lim free d)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hx : ∀ i, |x i|≤(U : ℤ)) :
    Meets lim (program fastP fastProc κ cutoff) (fastP.length+3) d [n,U,src,free] μ (LightBruteThreeSum.time n)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ ν=μ) := by sorry
