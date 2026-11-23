-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionDivision_exists_section
-- name    : ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:17.333548+00:00
-- url     : https://prove2.me/theorems/43038806-a936-4368-bac1-be3ef58a3eda
-- title:
--   Section Division: exists section
-- statement:
--   The Section Division construction uses the exists section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SectionDivision.lean#L16-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SectionDivision.lean#L16-L51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
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
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionDivision
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

theorem ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section {k : Type} [Field k] [IsAlgClosed k] {P' : Scheme.{0}}
    (p : P' ⟶ Spec (CommRingCat.of k)) [IsFinite p] [Surjective p] :
    ∃ t : Spec (CommRingCat.of k) ⟶ P', t ≫ p = 𝟙 _ := by sorry
