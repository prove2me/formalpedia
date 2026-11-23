-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_mul
-- name    : ReciprocityTheory.L2DbarEstimates.wd_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:49:50.615148+00:00
-- url     : https://prove2.me/theorems/ddaae39d-cf87-43c1-9470-39e240a369cd
-- title:
--   L2 Dbar Estimates: wd mul
-- statement:
--   The L2 Dbar Estimates construction uses the wd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L65-L72

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

theorem ReciprocityTheory.L2DbarEstimates.wd_mul {j : Fin n} {f g : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    wd n j (fun y => f y * g y) x = wd n j f x * g x + f x * wd n j g x := by sorry
