-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ValAt_periodic_const
-- name    : ReciprocityTheory.ChartRestriction.G.TB.ValAt.periodic_const
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:08.074875+00:00
-- url     : https://prove2.me/theorems/aedcf8d6-4419-5d4b-89d8-35c71f3a3ef2
-- title:
--   Val At: periodic const
-- statement:
--   The Val At construction uses the periodic const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ValAtLem.lean#L116-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ValAtLem.lean#L116-L126

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

theorem ReciprocityTheory.ChartRestriction.G.TB.ValAt.periodic_const (f : (Fin g → ℂ) → ℂ) (hf : Differentiable ℂ f) (L : AddSubgroup (Fin g → ℂ))
    (K : Set (Fin g → ℂ)) (hK : IsCompact K) (hcov : ∀ z, ∃ w ∈ K, z - w ∈ L)
    (hper : ∀ z, ∀ l ∈ L, f (z + l) = f z) (z w : Fin g → ℂ) : f z = f w := by sorry
