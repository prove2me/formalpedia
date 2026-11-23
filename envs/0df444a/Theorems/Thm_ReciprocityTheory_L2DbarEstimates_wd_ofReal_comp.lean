-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_ofReal_comp
-- name    : ReciprocityTheory.L2DbarEstimates.wd_ofReal_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:49:30.86437+00:00
-- url     : https://prove2.me/theorems/028ec8eb-f18f-4173-b81a-e4a30127ed4f
-- title:
--   L2 Dbar Estimates: wd of Real comp
-- statement:
--   The L2 Dbar Estimates construction uses the wd of Real comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L93-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L93-L104

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

theorem ReciprocityTheory.L2DbarEstimates.wd_ofReal_comp {j : Fin n} {k : ℝ → ℝ} {v : V n → ℝ} {x : V n}
    (hk : DifferentiableAt ℝ k (v x)) (hv : DifferentiableAt ℝ v x) :
    wd n j (fun y => (k (v y) : ℂ)) x = ((deriv k (v x) : ℝ) : ℂ) * wd n j (fun y => (v y : ℂ)) x := by sorry
