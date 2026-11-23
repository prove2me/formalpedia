-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr
-- name    : ReciprocityTheory.L2DbarEstimates.wd_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:11.052116+00:00
-- url     : https://prove2.me/theorems/069b1f3f-9832-4234-8094-a444821d7181
-- title:
--   L2 Dbar Estimates: wd congr
-- statement:
--   The L2 Dbar Estimates construction uses the wd congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L12-L14

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

theorem ReciprocityTheory.L2DbarEstimates.wd_congr {j : Fin n} {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) :
    wd n j f x = wd n j g x := by sorry
