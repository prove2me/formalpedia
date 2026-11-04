-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceCountHost_physical_count_spec
-- name    : ThreeSum.LightTernarySourceCountHost.physical_count_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:18:32.049119+00:00
-- url     : https://prove2.me/theorems/530d2895-0428-4a1e-b193-49dd5fd53b1f
-- title:
--   Light Ternary Source Count Host: physical count spec
-- statement:
--   The resulting literal wanted-row score is the exact factorial-scaled
--   weighted sum over physical original-record pairs in the same map bank.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L241-L278
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L241-L278

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_LightTernaryCountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_ThreeSum_LightTernarySourceCountHost
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernarySourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightTernarySourceCountHost.physical_count_spec {lim : Limits} {P : Program}
    {N a b p d t count dst keep : ℕ} (argv : List ℤ) (μ : ℕ → ℤ)
    (S T : Finset (ℕ × ℕ))
    (enumeration : ℕ → TernaryJointType.TritWord N)
    (leftKey leftGroup rightKey rightGroup : ℕ → ℕ)
    (leftWeight rightWeight : ℕ → ℤ)
    (group : ℕ → ℕ) (Q : ℕ → TernaryJointType.TritWord N)
    (hleft : ∀ pair∈S, TernaryBank.rank (enumeration (leftKey pair.2))=a)
    (hright : ∀ pair∈T, TernaryBank.rank (enumeration (rightKey pair.2))=b)
    (hQ : ∀ j<count, TernaryBank.rank (Q j)=a+b)
    (h : Meets lim P p d argv μ t (fun _ ν => Kept μ ν keep ∧ ∀ j<count,
      ν (dst+j)=LightTernaryWantedRows.score
        (fun g A => TernaryConvolution.factorial A*
          TernarySourceHostModel.physical S enumeration leftKey leftGroup leftWeight g A)
        (fun g B => TernaryConvolution.factorial B*
          TernarySourceHostModel.physical T enumeration rightKey rightGroup rightWeight g B)
        group Q j)) :
    Meets lim P p d argv μ t (fun _ ν => Kept μ ν keep ∧ ∀ j<count,
      ν (dst+j)=TernaryConvolution.factorial (Q j)*
        TernaryWeightedPhysicalSources.pairWeight
          (TernarySourceHostModel.channel S leftGroup (group j))
          (TernarySourceHostModel.channel T rightGroup (group j))
          (fun pair => enumeration (leftKey pair.2))
          (fun pair => enumeration (rightKey pair.2))
          (fun pair => leftWeight pair.1) (fun pair => rightWeight pair.1) (Q j)) := by sorry
