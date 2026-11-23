-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_fderiv_ofReal_apply
-- name    : ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:26.800203+00:00
-- url     : https://prove2.me/theorems/af4c50d1-d2ba-4bfd-bd05-0243f026777f
-- title:
--   L2 Dbar Estimates: fderiv of Real apply
-- statement:
--   The L2 Dbar Estimates construction uses the fderiv of Real apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L83-L87

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

theorem ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply {v : V n → ℝ} {x : V n} (hv : DifferentiableAt ℝ v x) (w : V n) :
    fderiv ℝ (fun y => (v y : ℂ)) x w = (fderiv ℝ v x w : ℂ) := by sorry
