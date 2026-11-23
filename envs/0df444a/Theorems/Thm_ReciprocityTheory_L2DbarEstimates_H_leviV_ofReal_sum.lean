-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviV_ofReal_sum
-- name    : ReciprocityTheory.L2DbarEstimates.H.leviV_ofReal_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:49.863071+00:00
-- url     : https://prove2.me/theorems/99d2b5ff-eb2c-4277-a8dd-126e93895354
-- title:
--   H: levi V of Real sum
-- statement:
--   The H construction uses the levi V of Real sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/LeviVA.lean#L120-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/LeviVA.lean#L120-L146

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.H.leviV_ofReal_sum {m : ℕ} {u : Fin m → V n → ℝ} {x : V n}
    (hu : ∀ i, ContDiffAt ℝ 2 (u i) x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((∑ i, u i y : ℝ) : ℂ)) x ξ = ∑ i, leviV n (fun y => (u i y : ℂ)) x ξ := by sorry
