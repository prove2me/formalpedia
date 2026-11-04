-- Prove2me | Theorems.Thm_ThreeSum_TernaryHybridCore_solves_of_fast
-- name    : ThreeSum.TernaryHybridCore.solves_of_fast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:40:21.637192+00:00
-- url     : https://prove2.me/theorems/772f639b-eec8-44bf-9b0d-6010abf010ea
-- title:
--   Ternary Hybrid Core: solves of fast
-- statement:
--   Compile the fully specified hybrid caller into the original 3SUM task
--   contract.  No change to the task, its distinct-position predicate, or its
--   calling convention occurs.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCore.lean#L185-L212
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCore.lean#L185-L212

import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_TernaryHybridCore
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridCore
open Light
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
variable (fastNeed : ℕ → ℕ → Need) (fastTime : ℕ → ℕ)

theorem ThreeSum.TernaryHybridCore.solves_of_fast {fastP : Program} {fastProc κ cutoff : ℕ}
    (hfast : ∀ {lim : Limits} {src n free d : ℕ},
      ∀ (x : Fin n → ℤ) (μ : ℕ → ℤ),
        cutoff ≤ n → 0 < n → src+n ≤ free →
        (fastNeed n (n^κ)).Ok lim free d →
        Seg μ src (List.ofFn x) → (∀ i, |x i| ≤ ((n^κ : ℕ) : ℤ)) →
        Meets lim fastP fastProc d [src,n,free] μ (fastTime n)
          (fun r ν => (r=0 ∨ r=1) ∧
            (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free)) :
    Solves s3Task (program fastP fastProc κ cutoff) (fastP.length+5)
      (time fastTime κ cutoff) (TernaryHybridResources.need fastNeed κ cutoff) := by sorry
