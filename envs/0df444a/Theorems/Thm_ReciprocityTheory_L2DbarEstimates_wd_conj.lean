-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_conj
-- name    : ReciprocityTheory.L2DbarEstimates.wd_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:54.34713+00:00
-- url     : https://prove2.me/theorems/a6f7668e-3936-417a-bbf6-e6ebf645b155
-- title:
--   L2 Dbar Estimates: wd conj
-- statement:
--   The L2 Dbar Estimates construction uses the wd conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L135-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L135-L139

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

theorem ReciprocityTheory.L2DbarEstimates.wd_conj {j : Fin n} {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x) :
    wd n j (fun y => conj (f y)) x = conj (wdb n j f x) := by sorry
