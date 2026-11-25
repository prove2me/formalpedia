-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_height_const_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.T0.height_const_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:15:46.820207+00:00
-- url     : https://prove2.me/theorems/c0b324d5-982b-432b-bcf4-8a227843bddf
-- title:
--   T0: height const eq zero
-- statement:
--   The T0 construction uses the height const eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/BlockSphereProbIsProbabilityMeasure.lean#L24-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/BlockSphereProbIsProbabilityMeasure.lean#L24-L67

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

theorem ReciprocityTheory.ChartRestriction.G.T0.height_const_eq_zero {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) (a : K) :
    ReciprocityTheory.MultiplicativeHeights.h0 (MvPolynomial.C a : MvPolynomial (Fin B × Fin n) K) = 0 := by sorry
