-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalFastProgramProof_meets_of_colors
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalFastProgramProof.meets_of_colors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T14:50:43.774064+00:00
-- url     : https://prove2.me/theorems/b13c9fa9-cea6-4edf-8f29-1ca3d41b13db
-- title:
--   meets_of_colors
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryFastProgramProof.lean#L51-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryFastProgramProof.lean#L51-L100

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryFastProgram
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGlobalPreludeTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryFastProgramProof
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalFastProgramProof
open Light LightWeightedGlobalFastProgram LightWeightedGlobalGlobalPrelude
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalFastProgramProof.meets_of_colors {lim : Limits} {M b p K κ n src free depth colorMain colorTime colorDepth : ℕ}
    [Fact p.Prime] (color : Program) (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hM : 1<M) (hb : 1<b) (hn : 0<n) (hsrc : src≤free)
    (H : (WeightedGlobalGlobalPreludeResources.need M b p K κ n (n^κ)).Ok lim free (depth+1))
    (hspace : scanFree M b p K κ n free+6≤lim.space)
    (hword : (LightColorScanHost.word n : ℤ)≤lim.word)
    (hd : depth+ColorParameters.count (LightColorParametersCosts.width n)+colorDepth+5≤lim.depth)
    (hcolor : ∀c<p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ)), ∀ν₀,
      Receipt M b p K κ n free c μ ν₀→
      ∀ (i : ℕ) (hi : i < ColorParameters.count (LightColorParametersCosts.width n)) (ν : ℕ→ℤ),
      Kept ν₀ ν (scanFree M b p K κ n free)→
      Seg ν (scanFree M b p K κ n free) (ColorParameters.fields (ColorParameters.parameter hi))→
      ∀dd, dd+colorDepth≤lim.depth→
      Meets lim (program M b p K κ color colorMain) (50+colorMain) dd
        [src,n,params free,scanFree M b p K κ n free,scanFree M b p K κ n free+6] ν colorTime
        (fun z ξ=>(z=0∨z=1) ∧ (z=1↔ColorClassLists.witness (ColorParameters.parameter hi) x) ∧
          Kept ν ξ (scanFree M b p K κ n free))) :
    Meets lim (program M b p K κ color colorMain) (mainEntry color) depth [src,n,free] μ
      (time M b p K κ colorTime n)
      (fun z ν=>(z=0∨z=1) ∧ (z=1↔Coloring.DistinctZeroSum x) ∧ Kept μ ν free) := by sorry
