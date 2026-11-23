-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviV_normSq_comp
-- name    : ReciprocityTheory.L2DbarEstimates.H.leviV_normSq_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:33.125853+00:00
-- url     : https://prove2.me/theorems/58bf4e84-652c-4fc2-8d36-30c18150a1a1
-- title:
--   H: levi V norm Sq comp
-- statement:
--   The H construction uses the levi V norm Sq comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/LeviVA.lean#L248-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/LeviVA.lean#L248-L274

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq

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

theorem ReciprocityTheory.L2DbarEstimates.H.leviV_normSq_comp {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) x ξ =
      ((Complex.normSq (∑ j, wd n j g x * ξ j) : ℝ) : ℂ) := by sorry
