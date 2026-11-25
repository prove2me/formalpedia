-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_exists_heightOne
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValPl.exists_heightOne
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:37:37.169583+00:00
-- url     : https://prove2.me/theorems/d1c5ce56-2199-5660-86ab-3c491e80fab7
-- title:
--   Val Pl: exists height One
-- statement:
--   The Val Pl construction uses the exists height One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraMapOLInjective.lean#L231-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraMapOLInjective.lean#L231-L246

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValPl
open IsDedekindDomain WithZero IsLocalRing
variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
variable (O F L)
include F

theorem ReciprocityTheory.ChartRestriction.G.T0.ValPl.exists_heightOne (Q : Ideal (integralClosure O L)) (hQ : Q.IsMaximal) :
    ∃ v : HeightOneSpectrum (integralClosure O L), v.asIdeal = Q := by sorry
