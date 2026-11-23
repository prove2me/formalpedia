-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_ofReal
-- name    : ReciprocityTheory.L2DbarEstimates.wdb_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:22.423774+00:00
-- url     : https://prove2.me/theorems/9ad7f132-f58f-4b34-80df-32269f31c00a
-- title:
--   L2 Dbar Estimates: wdb of Real
-- statement:
--   The L2 Dbar Estimates construction uses the wdb of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L119-L123

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

theorem ReciprocityTheory.L2DbarEstimates.wdb_ofReal {j : Fin n} {v : V n → ℝ} {x : V n} (hv : DifferentiableAt ℝ v x) :
    wdb n j (fun y => (v y : ℂ)) x = conj (wd n j (fun y => (v y : ℂ)) x) := by sorry
