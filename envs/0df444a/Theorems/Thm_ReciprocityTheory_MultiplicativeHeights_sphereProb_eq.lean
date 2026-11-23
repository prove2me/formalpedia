-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sphereProb_eq
-- name    : ReciprocityTheory.MultiplicativeHeights.sphereProb_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:52.074941+00:00
-- url     : https://prove2.me/theorems/d7ea535c-707b-4f2e-873e-b3d5270cece2
-- title:
--   Multiplicative Heights: sphere Prob eq
-- statement:
--   The Multiplicative Heights construction uses the sphere Prob eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreD.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreD.lean#L9-L12

import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreC
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric Set Real

theorem ReciprocityTheory.MultiplicativeHeights.sphereProb_eq (n : ℕ) : sphereProb n =
    ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ)⁻¹ •
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by sorry
