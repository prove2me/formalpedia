-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanS_lift
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.tanS_lift
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:08:58.01766+00:00
-- url     : https://prove2.me/theorems/a5654dae-acb2-47ab-a914-5a03ad160325
-- title:
--   Chart: tan S lift
-- statement:
--   The Chart construction uses the tan S lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L29-L41

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.tanS_lift {y' : sp (R₀ := S) (DualNumber A') ⟶ G} (hy' : TanS y') :
    ∃ m ∈ M, ∃ y : sp (R₀ := S) (DualNumber A) ⟶ G, TanS y ∧
      spMap (dualMapS (IsScalarTower.toAlgHom S A A')) ≫ y =
        spMap (scaleS (S := S) (algebraMap (Localization.Away s) A' m)) ≫ y' := by sorry
