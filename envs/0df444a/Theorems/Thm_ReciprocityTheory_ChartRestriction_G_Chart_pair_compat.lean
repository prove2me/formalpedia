-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pair_compat
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.pair_compat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:33:22.181709+00:00
-- url     : https://prove2.me/theorems/ace05d00-6389-414f-872d-f95c8a4f7697
-- title:
--   Chart: pair compat
-- statement:
--   The Chart construction uses the pair compat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PairCompat.lean#L28-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PairCompat.lean#L28-L54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PairCompat
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
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] [∀ s : S, Smooth (Gs G s).hom]
set_option maxHeartbeats 800000

theorem ReciprocityTheory.ChartRestriction.G.Chart.pair_compat (a b t : S) (C : Chart (Gs G a)) {y₀ : sp (R₀ := S) (DualNumber (Localization.Away t)) ⟶ G}
    {za : sp (R₀ := S) (DualNumber (Localization.Away a)) ⟶ G} {zb : sp (R₀ := S) (DualNumber (Localization.Away b)) ⟶ G}
    (ha : TanS za) (hb : TanS zb) (N₁ : ℕ)
    (har : spMap (dualMapS (qL a t)) ≫ za =
      spMap (scaleS (S := S) (algebraMap S (Qv a t) t ^ N₁)) ≫ spMap (dualMapS (qR a t)) ≫ y₀)
    (hbr : spMap (dualMapS (qL b t)) ≫ zb =
      spMap (scaleS (S := S) (algebraMap S (Qv b t) t ^ N₁)) ≫ spMap (dualMapS (qR b t)) ≫ y₀) :
    ∃ M : ℕ, spMap (scaleS (S := S) (algebraMap S (Qv a b) t ^ M)) ≫ spMap (dualMapS (qL a b)) ≫ za =
      spMap (scaleS (S := S) (algebraMap S (Qv a b) t ^ M)) ≫ spMap (dualMapS (qR a b)) ≫ zb := by sorry
