-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_glue_tan
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.glue_tan
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:02:14.795851+00:00
-- url     : https://prove2.me/theorems/54c2cab7-738a-4d33-8e4d-47537b4d3ccd
-- title:
--   Chart: glue tan
-- statement:
--   The Chart construction uses the glue tan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSOfIdToRingHom.lean#L116-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSOfIdToRingHom.lean#L116-L208

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanSRestrict
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
set_option backward.isDefEq.respectTransparency false

theorem ReciprocityTheory.ChartRestriction.G.Chart.glue_tan {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    (w : ∀ k, sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G) (hw : ∀ k, TanS (w k))
    (hc : ∀ k l (T : CommRingCat.{0}) (α : DualNumber (Localization.Away (s k)) →+* T)
      (β : DualNumber (Localization.Away (s l)) →+* T), α.comp (dAway (s k)) = β.comp (dAway (s l)) →
      Spec.map (CommRingCat.ofHom α) ≫ (w k).left = Spec.map (CommRingCat.ofHom β) ≫ (w l).left) :
    ∃ v : sp (R₀ := S) (DualNumber S) ⟶ G, TanS v ∧
      ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v = w k := by sorry
