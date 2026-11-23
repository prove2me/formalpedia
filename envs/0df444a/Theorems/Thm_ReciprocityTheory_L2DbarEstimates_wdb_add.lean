-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_add
-- name    : ReciprocityTheory.L2DbarEstimates.wdb_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:44:13.338895+00:00
-- url     : https://prove2.me/theorems/5ec2516e-c511-4d64-8180-6bfec0b04393
-- title:
--   L2 Dbar Estimates: wdb add
-- statement:
--   The L2 Dbar Estimates construction uses the wdb add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L36-L41

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

theorem ReciprocityTheory.L2DbarEstimates.wdb_add {j : Fin n} {f g : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : wdb n j (fun y => f y + g y) x = wdb n j f x + wdb n j g x := by sorry
