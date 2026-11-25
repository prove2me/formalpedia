-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanS_away_uniq
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.tanS_away_uniq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:34:30.776332+00:00
-- url     : https://prove2.me/theorems/f9153ae7-64c9-5c18-a87d-f5e5936e745f
-- title:
--   Chart: tan S away uniq
-- statement:
--   The Chart construction uses the tan S away uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ScalePowMono.lean#L84-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ScalePowMono.lean#L84-L104

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
variable [∀ s : S, Smooth (Gs G s).hom]

theorem ReciprocityTheory.ChartRestriction.G.Chart.tanS_away_uniq {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A]
    [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A] (t : S)
    {y₁ y₂ : sp (R₀ := S) (DualNumber A) ⟶ G} (h₁ : TanS y₁) (h₂ : TanS y₂)
    (he : spMap (dualMapS (IsScalarTower.toAlgHom S A (Localization.Away (algebraMap S A t)))) ≫ y₁ =
      spMap (dualMapS (IsScalarTower.toAlgHom S A (Localization.Away (algebraMap S A t)))) ≫ y₂) :
    ∃ N : ℕ, spMap (scaleS (S := S) (algebraMap S A t ^ N)) ≫ y₁ = spMap (scaleS (algebraMap S A t ^ N)) ≫ y₂ := by sorry
