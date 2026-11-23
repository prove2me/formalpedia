-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_fderiv_conj_apply
-- name    : ReciprocityTheory.L2DbarEstimates.fderiv_conj_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:32.259751+00:00
-- url     : https://prove2.me/theorems/ee88f158-5978-4d79-920c-cc6be1f801b5
-- title:
--   L2 Dbar Estimates: fderiv conj apply
-- statement:
--   The L2 Dbar Estimates construction uses the fderiv conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L125-L129

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

theorem ReciprocityTheory.L2DbarEstimates.fderiv_conj_apply {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x) (w : V n) :
    fderiv ℝ (fun y => conj (f y)) x w = conj (fderiv ℝ f x w) := by sorry
