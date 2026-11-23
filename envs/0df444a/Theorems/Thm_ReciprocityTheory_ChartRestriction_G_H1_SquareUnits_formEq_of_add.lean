-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_formEq_of_add
-- name    : ReciprocityTheory.ChartRestriction.G.H1.SquareUnits.formEq_of_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:03.958573+00:00
-- url     : https://prove2.me/theorems/52259c35-747c-4644-b9e7-0d80ce40d307
-- title:
--   Square Units: form Eq of add
-- statement:
--   The Square Units construction uses the form Eq of add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SquareUnits.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SquareUnits.lean#L36-L41

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TopologicalSpace Opposite
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
variable {X Y Z : Scheme.{0}}
variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.H1.SquareUnits.formEq_of_add {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : ∀ (U : Type) [AddCommGroup U] (h : (Y ⟶ X) → U), ∑ k, ε k • h (φ k) = ∑ k, ε' k • h (φ' k)) :
    FormEq φ ε φ' ε' := by sorry
