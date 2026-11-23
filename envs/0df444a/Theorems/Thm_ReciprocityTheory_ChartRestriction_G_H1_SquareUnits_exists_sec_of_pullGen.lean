-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_exists_sec_of_pullGen
-- name    : ReciprocityTheory.ChartRestriction.G.H1.SquareUnits.exists_sec_of_pullGen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:32.582811+00:00
-- url     : https://prove2.me/theorems/8151d257-b364-4cc7-ace5-14ee3fe4ee21
-- title:
--   Square Units: exists sec of pull Gen
-- statement:
--   The Square Units construction uses the exists sec of pull Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SquareUnits.lean#L43-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SquareUnits.lean#L43-L67

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

theorem ReciprocityTheory.ChartRestriction.G.H1.SquareUnits.exists_sec_of_pullGen {Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y)
    (c : LB.Gen ((LB.LinComb L φ ε).pull h)) (hc : c.IsGen) :
    ∃ s : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε), ∀ (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι),
      Good L z J → IsUnit (sval s r z J) := by sorry
