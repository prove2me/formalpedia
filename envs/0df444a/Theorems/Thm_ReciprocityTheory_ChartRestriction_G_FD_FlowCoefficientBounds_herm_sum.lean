-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowCoefficientBounds_herm_sum
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.herm_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:13:59.141705+00:00
-- url     : https://prove2.me/theorems/3f4bf034-2454-566c-a7bd-eaa89e2bdda8
-- title:
--   Flow Coefficient Bounds: herm sum
-- statement:
--   The Flow Coefficient Bounds construction uses the herm sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowCoefficientBounds.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowCoefficientBounds.lean#L152-L156

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowIsotropicPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bNormHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.herm_sum {n : ℕ} (ω : Fin n → X.Ψ → Fin 2 → Fin 2 → ℂ) (hω : ∀ j, IsHermFam (ω j))
    (t : Fin n → ℝ) : IsHermFam (∑ j, (t j : ℂ) • ω j) := by sorry
