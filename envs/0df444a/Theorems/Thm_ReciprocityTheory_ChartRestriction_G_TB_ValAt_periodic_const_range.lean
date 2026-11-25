-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ValAt_periodic_const_range
-- name    : ReciprocityTheory.ChartRestriction.G.TB.ValAt.periodic_const_range
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:27:03.368984+00:00
-- url     : https://prove2.me/theorems/a4dc4ad5-14b0-4f4c-8174-be1caa9874fb
-- title:
--   Val At: periodic const range
-- statement:
--   The Val At construction uses the periodic const range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ValAtLem.lean#L128-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ValAtLem.lean#L128-L159

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.ValAt
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X : Scheme.{0}}
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.ValAt.periodic_const_range {La : Type} [AddCommGroup La] (P : La →+ (Fin g → ℂ))
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) (f : (Fin g → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ z a, f (z + P a) = f z) (z w : Fin g → ℂ) : f z = f w := by sorry
