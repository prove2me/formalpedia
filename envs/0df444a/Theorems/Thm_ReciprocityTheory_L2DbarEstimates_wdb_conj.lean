-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_conj
-- name    : ReciprocityTheory.L2DbarEstimates.wdb_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:49.485657+00:00
-- url     : https://prove2.me/theorems/ca759da5-ac96-44f8-a22a-554e9e115b0f
-- title:
--   L2 Dbar Estimates: wdb conj
-- statement:
--   The L2 Dbar Estimates construction uses the wdb conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L141-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L141-L145

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

theorem ReciprocityTheory.L2DbarEstimates.wdb_conj {j : Fin n} {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x) :
    wdb n j (fun y => conj (f y)) x = conj (wd n j f x) := by sorry
