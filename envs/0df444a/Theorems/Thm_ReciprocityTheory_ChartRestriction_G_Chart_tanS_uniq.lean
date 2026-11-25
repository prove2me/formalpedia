-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanS_uniq
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.tanS_uniq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:18:03.311814+00:00
-- url     : https://prove2.me/theorems/ccbc84d2-7f8c-59fc-a5aa-7c826de12887
-- title:
--   Chart: tan S uniq
-- statement:
--   The Chart construction uses the tan S uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L44-L52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
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
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] {s : S} (C : Chart (Gs G s))
  [Algebra.FinitePresentation (Localization.Away s) Γ((Gs G s).left, C.U)]
  {A : Type} [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A]
  {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A'] [IsScalarTower S (Localization.Away s) A']
  [Algebra A A'] [IsScalarTower (Localization.Away s) A A'] [IsScalarTower S A A']
  (M : Submonoid (Localization.Away s)) [IsLocalization (Algebra.algebraMapSubmonoid A M) A']
include C

theorem ReciprocityTheory.ChartRestriction.G.Chart.tanS_uniq {y₁ y₂ : sp (R₀ := S) (DualNumber A) ⟶ G} (h₁ : TanS y₁) (h₂ : TanS y₂)
    (he : spMap (dualMapS (IsScalarTower.toAlgHom S A A')) ≫ y₁ = spMap (dualMapS (IsScalarTower.toAlgHom S A A')) ≫ y₂) :
    ∃ m ∈ M, spMap (scaleS (S := S) (algebraMap (Localization.Away s) A m)) ≫ y₁ =
      spMap (scaleS (S := S) (algebraMap (Localization.Away s) A m)) ≫ y₂ := by sorry
