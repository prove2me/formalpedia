-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscVal_addv_nonneg_iff
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HDiscVal.addv_nonneg_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:36:54.232044+00:00
-- url     : https://prove2.me/theorems/76afd30c-a585-5b3c-a77b-dee0fb4d8f06
-- title:
--   HDisc Val: addv nonneg iff
-- statement:
--   The HDisc Val construction uses the addv nonneg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAC.lean#L100-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAC.lean#L100-L116

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscVal
open IsDedekindDomain WithZero ValPl
variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
omit [IsFractionRing O F] [FiniteDimensional F L] [Algebra.IsSeparable F L] [IsScalarTower O F L]

theorem ReciprocityTheory.ChartRestriction.G.T0.HDiscVal.addv_nonneg_iff (v : HeightOneSpectrum (integralClosure O L)) {y : L} (hy : y ≠ 0) :
    0 ≤ addv L v y ↔ v.valuation L y ≤ 1 := by sorry
