-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_blockSphereProb_isProbabilityMeasure
-- name    : ReciprocityTheory.ChartRestriction.G.T0.blockSphereProb_isProbabilityMeasure
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:36:19.913798+00:00
-- url     : https://prove2.me/theorems/d845a51f-7ee6-4d4d-8459-6f2140d41758
-- title:
--   T0: block Sphere Prob is Probability Measure
-- statement:
--   The T0 construction uses the block Sphere Prob is Probability Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/BlockSphereProbIsProbabilityMeasure.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/BlockSphereProbIsProbabilityMeasure.lean#L7-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockSphereProbIsProbabilityMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField

theorem ReciprocityTheory.ChartRestriction.G.T0.blockSphereProb_isProbabilityMeasure {B n : ℕ} (hn : 0 < n) :
    MeasureTheory.IsProbabilityMeasure (ReciprocityTheory.MultiplicativeHeights.blockSphereProb B n) := by sorry
