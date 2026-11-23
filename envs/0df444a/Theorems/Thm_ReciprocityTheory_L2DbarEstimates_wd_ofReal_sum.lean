-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_ofReal_sum
-- name    : ReciprocityTheory.L2DbarEstimates.wd_ofReal_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:50.838244+00:00
-- url     : https://prove2.me/theorems/10128b97-b75a-4ad3-affa-14187882da37
-- title:
--   L2 Dbar Estimates: wd of Real sum
-- statement:
--   The L2 Dbar Estimates construction uses the wd of Real sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/OfRealNormSqSumMul.lean#L82-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/OfRealNormSqSumMul.lean#L82-L87

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
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

theorem ReciprocityTheory.L2DbarEstimates.wd_ofReal_sum {m : ℕ} {j : Fin n} {u : Fin m → V n → ℝ} {x : V n}
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) :
    wd n j (fun y => ((∑ i, u i y : ℝ) : ℂ)) x = ∑ i, wd n j (fun y => (u i y : ℂ)) x := by sorry
