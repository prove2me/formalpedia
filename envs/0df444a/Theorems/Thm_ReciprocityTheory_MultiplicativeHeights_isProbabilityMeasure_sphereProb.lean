-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_isProbabilityMeasure_sphereProb
-- name    : ReciprocityTheory.MultiplicativeHeights.isProbabilityMeasure_sphereProb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:39.082873+00:00
-- url     : https://prove2.me/theorems/56c8e704-2d49-4646-b287-c5149911077d
-- title:
--   Multiplicative Heights: is Probability Measure sphere Prob
-- statement:
--   The Multiplicative Heights construction uses the is Probability Measure sphere Prob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusC.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusC.lean#L23-L28

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusC
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
open MeasureTheory Metric
open scoped Pointwise

theorem ReciprocityTheory.MultiplicativeHeights.isProbabilityMeasure_sphereProb {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (sphereProb n) := by sorry
