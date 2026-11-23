-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_ofReal_comp
-- name    : ReciprocityTheory.L2DbarEstimates.wdb_ofReal_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:17.909372+00:00
-- url     : https://prove2.me/theorems/de35ae1e-e2ee-4592-ae8f-26bc3a7a11df
-- title:
--   L2 Dbar Estimates: wdb of Real comp
-- statement:
--   The L2 Dbar Estimates construction uses the wdb of Real comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L106-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L106-L117

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

theorem ReciprocityTheory.L2DbarEstimates.wdb_ofReal_comp {j : Fin n} {k : ℝ → ℝ} {v : V n → ℝ} {x : V n}
    (hk : DifferentiableAt ℝ k (v x)) (hv : DifferentiableAt ℝ v x) :
    wdb n j (fun y => (k (v y) : ℂ)) x = ((deriv k (v x) : ℝ) : ℂ) * wdb n j (fun y => (v y : ℂ)) x := by sorry
