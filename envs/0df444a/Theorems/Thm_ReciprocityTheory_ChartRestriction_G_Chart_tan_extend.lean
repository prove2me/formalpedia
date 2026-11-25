-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tan_extend
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.tan_extend
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:33:45.155504+00:00
-- url     : https://prove2.me/theorems/62001c30-2ec9-4999-83aa-9cb9a41415d6
-- title:
--   Chart: tan extend
-- statement:
--   The Chart construction uses the tan extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PairCompat.lean#L57-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PairCompat.lean#L57-L100

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.tan_extend {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤) (C : ∀ k, Chart (Gs G (s k)))
    (k0 : Fin n) {y₀ : sp (R₀ := S) (DualNumber (Localization.Away (s k0))) ⟶ G} (hy₀ : TanS y₀) :
    ∃ N : ℕ, ∃ w : sp (R₀ := S) (DualNumber S) ⟶ G, TanS w ∧
      spMap (dualMapS (Algebra.ofId S (Localization.Away (s k0)))) ≫ w =
        spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k0)) (s k0) ^ N)) ≫ y₀ := by sorry
