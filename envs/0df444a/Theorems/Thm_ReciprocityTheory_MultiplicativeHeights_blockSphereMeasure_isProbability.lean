-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockSphereMeasure_isProbability
-- name    : ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_isProbability
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:22.075317+00:00
-- url     : https://prove2.me/theorems/3fa8cfb8-163b-452f-ac8e-7eff7ea670c1
-- title:
--   Multiplicative Heights: block Sphere Measure is Probability
-- statement:
--   The Multiplicative Heights construction uses the block Sphere Measure is Probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L19-L23

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

theorem ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_isProbability {B n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (blockSphereProb B n) := by sorry
