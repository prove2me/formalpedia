-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_wd_ofReal_sum
-- name    : ReciprocityTheory.L2DbarEstimates.H.wd_ofReal_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:30:38.610867+00:00
-- url     : https://prove2.me/theorems/8de6a042-8ae3-4bb8-8aaa-c691e0e133a3
-- title:
--   H: wd of Real sum
-- statement:
--   The H construction uses the wd of Real sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/LeviVA.lean#L59-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/LeviVA.lean#L59-L73

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

theorem ReciprocityTheory.L2DbarEstimates.H.wd_ofReal_sum {m : ℕ} {j : Fin n} {u : Fin m → V n → ℝ} {x : V n}
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) :
    wd n j (fun y => ((∑ i, u i y : ℝ) : ℂ)) x = ∑ i, wd n j (fun y => (u i y : ℂ)) x := by sorry
