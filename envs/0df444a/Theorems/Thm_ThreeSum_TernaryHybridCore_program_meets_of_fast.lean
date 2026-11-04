-- Prove2me | Theorems.Thm_ThreeSum_TernaryHybridCore_program_meets_of_fast
-- name    : ThreeSum.TernaryHybridCore.program_meets_of_fast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:40:31.650934+00:00
-- url     : https://prove2.me/theorems/85dde62f-27b7-4576-a416-ee6183ac75cd
-- title:
--   Ternary Hybrid Core: program meets of fast
-- statement:
--   The fast branch law uses its own resource need and running time.  Its
--   successful guards provide the complete original input magnitude condition.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCore.lean#L153-L180
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCore.lean#L153-L180

import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_TernaryHybridCore
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridCore
open Light
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
variable (fastNeed : ℕ → ℕ → Need) (fastTime : ℕ → ℕ)

theorem ThreeSum.TernaryHybridCore.program_meets_of_fast {lim : Limits} {fastP : Program}
    {fastProc κ cutoff src n U free d : ℕ}
    (x : Fin n → ℤ) (μ : ℕ → ℤ) (hn : 0 < n) (hsrc : src+n ≤ free)
    (H : (TernaryHybridResources.need fastNeed κ cutoff n U).Ok lim free d)
    (hinput : Seg μ src (List.ofFn x)) (hx : ∀ i, |x i| ≤ (U : ℤ))
    (hfast : ∀ {lim : Limits} {src n free d : ℕ},
      ∀ (x : Fin n → ℤ) (μ : ℕ → ℤ),
        cutoff ≤ n → 0 < n → src+n ≤ free →
        (fastNeed n (n^κ)).Ok lim free d →
        Seg μ src (List.ofFn x) → (∀ i, |x i| ≤ ((n^κ : ℕ) : ℤ)) →
        Meets lim fastP fastProc d [src,n,free] μ (fastTime n)
          (fun r ν => (r=0 ∨ r=1) ∧
            (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free)) :
    Meets lim (program fastP fastProc κ cutoff) (fastP.length+5) d
      [n,U,src,free] μ (time fastTime κ cutoff n U)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free) := by sorry
