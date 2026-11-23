-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_of_differentiableAt
-- name    : ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:51.805806+00:00
-- url     : https://prove2.me/theorems/c456b74e-b900-4e44-a6a0-ed987adb4ce1
-- title:
--   L2 Dbar Estimates: wdb of differentiable At
-- statement:
--   The L2 Dbar Estimates construction uses the wdb of differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L152-L156

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

theorem ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt {j : Fin n} {f : V n → ℂ} {x : V n}
    (hf : DifferentiableAt ℂ f x) : wdb n j f x = 0 := by sorry
