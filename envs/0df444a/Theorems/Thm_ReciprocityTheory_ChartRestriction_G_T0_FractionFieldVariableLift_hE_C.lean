-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FractionFieldVariableLift_hE_C
-- name    : ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.hE_C
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:36:30.655652+00:00
-- url     : https://prove2.me/theorems/e3790267-b5a8-41f5-b4fe-1615eb202b35
-- title:
--   Fraction Field Variable Lift: h E C
-- statement:
--   The Fraction Field Variable Lift construction uses the h E C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OffBaseSubstitution.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OffBaseSubstitution.lean#L75-L77

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

theorem ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.hE_C (j0 : Fin (N + 1)) (r : Ω) :
    hE Ω D N j0 (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by sorry
