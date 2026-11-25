-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tan_prime_lift
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.tan_prime_lift
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:57:43.922213+00:00
-- url     : https://prove2.me/theorems/a5dcd3ca-beb8-4e9d-b366-f8fb3bf298e9
-- title:
--   Chart: tan prime lift
-- statement:
--   The Chart construction uses the tan prime lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ExistsAwayNotMem.lean#L38-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ExistsAwayNotMem.lean#L38-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PairCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsAwayNotMem
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
variable (p : Ideal S) [p.IsPrime]

theorem ReciprocityTheory.ChartRestriction.G.Chart.tan_prime_lift {y' : sp (R₀ := S) (DualNumber (Localization.AtPrime p)) ⟶ G} (hy' : TanS y') :
    ∃ q ∈ p.primeCompl, ∃ w : sp (R₀ := S) (DualNumber S) ⟶ G, TanS w ∧
      spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ w =
        spMap (scaleS (S := S) (algebraMap S (Localization.AtPrime p) q)) ≫ y' := by sorry
