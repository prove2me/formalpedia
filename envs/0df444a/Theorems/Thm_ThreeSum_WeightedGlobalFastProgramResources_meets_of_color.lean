-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFastProgramResources_meets_of_color
-- name    : ThreeSum.WeightedGlobalFastProgramResources.meets_of_color
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:57:00.189204+00:00
-- url     : https://prove2.me/theorems/25d0518f-87d8-46e0-944c-8cde1b3aac17
-- title:
--   Weighted Global Fast Program Resources: meets of color
-- statement:
--   Resource and entry composition for the real fast program. The child
--   contract is stated for the literal per-color program before relocation.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L97-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L97-L118

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFastProgramResources
open Light LightWeightedGlobalFastProgram LightWeightedGlobalFastProgramProof
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalFastProgramResources.meets_of_color {lim : Limits} {M b p K κ n src free depth colorMain colorTime : ℕ}
    [Fact p.Prime] (color : Program) (colorNeed : ℕ→ℕ→Need) (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hM : 1<M) (hb : 1<b) (hn : 0<n) (hsrc : src≤free)
    (H : (need M b p K κ colorNeed n (n^κ)).Ok lim free depth)
    (hcolor : ∀c<p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ)), ∀ν₀,
      Receipt M b p K κ n free c μ ν₀→
      ∀ (i : ℕ) (hi : i < ColorParameters.count (LightColorParametersCosts.width n)) (ν : ℕ→ℤ),
      Kept ν₀ ν (scanFree M b p K κ n free)→
      Seg ν (scanFree M b p K κ n free) (ColorParameters.fields (ColorParameters.parameter hi))→
      ∀dd, (colorNeed n (n^κ)).Ok lim (scanFree M b p K κ n free+6) dd→
      Meets lim color colorMain dd
        [src,n,LightWeightedGlobalGlobalPrelude.params free,scanFree M b p K κ n free,
          scanFree M b p K κ n free+6] ν colorTime
        (fun z ξ=>(z=0∨z=1) ∧ (z=1↔ColorClassLists.witness (ColorParameters.parameter hi) x) ∧
          Kept ν ξ (scanFree M b p K κ n free))) :
    Meets lim (program M b p K κ color colorMain) (mainEntry color) depth [src,n,free] μ
      (time M b p K κ colorTime n)
      (fun z ν=>(z=0∨z=1) ∧ (z=1↔Coloring.DistinctZeroSum x) ∧ Kept μ ν free) := by sorry
