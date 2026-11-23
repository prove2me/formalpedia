-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_isUnit_sval
-- name    : ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.isUnit_sval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:31:39.952445+00:00
-- url     : https://prove2.me/theorems/cd633258-f368-4c27-9bdf-4517b97858d7
-- title:
--   Section Arithmetic: is Unit sval
-- statement:
--   The Section Arithmetic construction uses the is Unit sval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SectionArithmetic.lean#L137-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SectionArithmetic.lean#L137-L149

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.isUnit_sval {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (k : (LB.LinComb L φ ε).ι) (hk : r z ∈ Y.basicOpen (s.f k)) :
    IsUnit (sval s r z J) := by sorry
