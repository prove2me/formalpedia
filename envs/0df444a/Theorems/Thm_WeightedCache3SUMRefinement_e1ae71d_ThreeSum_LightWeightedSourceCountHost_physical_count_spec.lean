-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_physical_count_spec
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.physical_count_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:18:38.76547+00:00
-- url     : https://prove2.me/theorems/4b18f4d8-b964-4470-930f-faed1eca1ec3
-- title:
--   physical_count_spec
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/SourceCountHost.lean#L246-L283
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/SourceCountHost.lean#L246-L283

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.physical_count_spec {lim : Limits} {P : Program}
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
      ν (dst+j)=LightWeightedWantedRows.score
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
