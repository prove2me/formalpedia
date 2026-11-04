-- Prove2me | Theorems.Thm_ThreeSum_TernaryHybridCore_program_meets
-- name    : ThreeSum.TernaryHybridCore.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:03:30.309512+00:00
-- url     : https://prove2.me/theorems/8ab34faf-6dd5-4206-bfb0-f55d9fde0c7b
-- title:
--   Ternary Hybrid Core: program meets
-- statement:
--   The branch law is consumed only after both runtime guards succeed. The
--       concrete fast module must discharge it using its actual executable.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCore.lean#L82-L149
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCore.lean#L82-L149

import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_TernaryHybridCore
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightClassFilter_program_meets
import Theorems.Thm_ThreeSum_LightColorIndex_program_meets
import Theorems.Thm_ThreeSum_LightColorParameters_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightNatPower_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridCore
open Light
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
variable (fastNeed : ℕ → ℕ → Need) (fastTime : ℕ → ℕ)

theorem ThreeSum.TernaryHybridCore.program_meets {lim : Limits} {fastP : Program} {fastProc κ cutoff src n U free d : ℕ}
    (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hn : 0<n) (hsrc : src+n≤free)
    (H : (TernaryHybridResources.need fastNeed κ cutoff n U).Ok lim free d)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hx : ∀ i, |x i|≤(U : ℤ))
    (hfast : cutoff≤n → U≤n^κ →
      Meets lim fastP fastProc (d+1) [src,n,free] μ
        (fastTime n)
        (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free)) :
    Meets lim (program fastP fastProc κ cutoff) (fastP.length+5) d [n,U,src,free] μ
      (time fastTime κ cutoff n U)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free) := by sorry
