-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tan_ext_cover
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.tan_ext_cover
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:18:10.774495+00:00
-- url     : https://prove2.me/theorems/3eb2f5fa-ca19-5003-b29f-28955c272e4a
-- title:
--   Chart: tan ext cover
-- statement:
--   The Chart construction uses the tan ext cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L201-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L201-L217

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
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
set_option backward.isDefEq.respectTransparency false

theorem ReciprocityTheory.ChartRestriction.G.Chart.tan_ext_cover {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    {v₁ v₂ : sp (R₀ := S) (DualNumber S) ⟶ G}
    (h : ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v₁ =
      spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v₂) : v₁ = v₂ := by sorry
