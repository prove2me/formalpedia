-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FractionFieldVariableLift_hL_X
-- name    : ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.hL_X
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:36:28.484854+00:00
-- url     : https://prove2.me/theorems/ae6a5559-6c04-4f07-b72f-6b9583b41f5e
-- title:
--   Fraction Field Variable Lift: h L X
-- statement:
--   The Fraction Field Variable Lift construction uses the h L X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OffBaseSubstitution.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OffBaseSubstitution.lean#L62-L66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteDimensionalOfLiftY
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OffBaseSubstitution
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
open ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift
variable {K : Type} [Field K] {Ω : Type} [Field Ω] {D N : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.hL_X (v : TVar D N) : hL K D N (MvPolynomial.X v) =
    if h : v.1 = 0 then MvPolynomial.X v.2 else MvPolynomial.C (MvPolynomial.X ⟨v, h⟩) := by sorry
