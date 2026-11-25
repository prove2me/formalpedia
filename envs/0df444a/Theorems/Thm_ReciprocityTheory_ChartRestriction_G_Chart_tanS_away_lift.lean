-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanS_away_lift
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.tanS_away_lift
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:21:01.761087+00:00
-- url     : https://prove2.me/theorems/41f6c8b8-3e25-4339-9359-18b9236dd9f4
-- title:
--   Chart: tan S away lift
-- statement:
--   The Chart construction uses the tan S away lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ScalePowMono.lean#L63-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ScalePowMono.lean#L63-L82

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.tanS_away_lift {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A]
    [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A] (t : S)
    {y' : sp (R₀ := S) (DualNumber (Localization.Away (algebraMap S A t))) ⟶ G} (hy' : TanS y') :
    ∃ N : ℕ, ∃ y : sp (R₀ := S) (DualNumber A) ⟶ G, TanS y ∧
      spMap (dualMapS (IsScalarTower.toAlgHom S A (Localization.Away (algebraMap S A t)))) ≫ y =
        spMap (scaleS (S := S) (algebraMap S (Localization.Away (algebraMap S A t)) t ^ N)) ≫ y' := by sorry
