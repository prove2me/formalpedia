-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_map_ne_zero_of_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.G.T0.map_ne_zero_of_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:47.687367+00:00
-- url     : https://prove2.me/theorems/bfcfb0df-e792-5e3b-8e6e-0c25ac4fb8d1
-- title:
--   T0: map ne zero of ne zero
-- statement:
--   The T0 construction uses the map ne zero of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ContinuousTorusPoint.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ContinuousTorusPoint.lean#L12-L13

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ContinuousTorusPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed
variable {K : Type} [Field K] [NumberField K] {κ : Type} [Fintype κ]

theorem ReciprocityTheory.ChartRestriction.G.T0.map_ne_zero_of_ne_zero {f : MvPolynomial κ K} (hf : f ≠ 0) (σ : K →+* ℂ) :
    MvPolynomial.map σ f ≠ 0 := by sorry
