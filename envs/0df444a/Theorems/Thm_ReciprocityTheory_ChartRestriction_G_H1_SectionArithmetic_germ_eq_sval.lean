-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_germ_eq_sval
-- name    : ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.germ_eq_sval
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:49.145429+00:00
-- url     : https://prove2.me/theorems/31e766c2-e558-4ec6-bfdf-57830c6d9b70
-- title:
--   Section Arithmetic: germ eq sval
-- statement:
--   The Section Arithmetic construction uses the germ eq sval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SectionArithmetic.lean#L127-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SectionArithmetic.lean#L127-L135

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

theorem ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.germ_eq_sval {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (y : Y)
    {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) (j : K → L.ι) (hy : y ∈ LB.wchart L φ j) :
    (Y.presheaf.germ (LB.wchart L φ j) y hy).hom (s.f j) =
      (trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * sval s (𝟙 Y) y J := by sorry
