-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_placesOver_iff_loc
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValPl.placesOver_iff_loc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:55.677683+00:00
-- url     : https://prove2.me/theorems/d2f93f76-affc-476e-af0a-a2529c8c32f1
-- title:
--   Val Pl: places Over iff loc
-- statement:
--   The Val Pl construction uses the places Over iff loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraMapOLInjective.lean#L184-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraMapOLInjective.lean#L184-L212

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

theorem ReciprocityTheory.ChartRestriction.G.T0.ValPl.placesOver_iff_loc {R O L : Type*} [CommRing R] [CommRing O] [IsLocalRing O] [Field L]
    [Algebra R O] [Algebra R L] [Algebra O L] [IsScalarTower R O L] (P : Ideal R) [P.IsPrime]
    [IsLocalization.AtPrime O P] (w : AddValuation L (WithTop ℤ)) :
    (∀ x : R, 0 ≤ w (algebraMap R L x) ∧ (0 < w (algebraMap R L x) ↔ x ∈ P)) ↔
      (∀ x : O, 0 ≤ w (algebraMap O L x) ∧ (0 < w (algebraMap O L x) ↔ x ∈ maximalIdeal O)) := by sorry
