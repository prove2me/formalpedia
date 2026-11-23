-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sphereMeasure_isProbability
-- name    : ReciprocityTheory.MultiplicativeHeights.sphereMeasure_isProbability
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:08.723688+00:00
-- url     : https://prove2.me/theorems/8d6d7485-115a-4ea7-b551-5ed7611271b9
-- title:
--   Multiplicative Heights: sphere Measure is Probability
-- statement:
--   The Multiplicative Heights construction uses the sphere Measure is Probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L9-L17

import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
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
open MeasureTheory MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.sphereMeasure_isProbability {n : ℕ} (hn : 0 < n) : IsProbabilityMeasure (sphereProb n) := by sorry
