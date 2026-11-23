-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_sum
-- name    : ReciprocityTheory.L2DbarEstimates.wd_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:13.235866+00:00
-- url     : https://prove2.me/theorems/26227857-e489-4d08-9ec2-28b723128c13
-- title:
--   L2 Dbar Estimates: wd sum
-- statement:
--   The L2 Dbar Estimates construction uses the wd sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L43-L52

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.wd_sum {ι : Type*} (s : Finset ι) {j : Fin n} {f : ι → V n → ℂ} {x : V n}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    wd n j (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, wd n j (f i) x := by sorry
