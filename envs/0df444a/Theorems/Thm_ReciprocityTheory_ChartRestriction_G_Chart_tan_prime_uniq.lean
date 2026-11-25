-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tan_prime_uniq
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.tan_prime_uniq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:42.487897+00:00
-- url     : https://prove2.me/theorems/48557cb5-8426-5f3b-8719-c3b5e2cbaaa1
-- title:
--   Chart: tan prime uniq
-- statement:
--   The Chart construction uses the tan prime uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ExistsAwayNotMem.lean#L66-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ExistsAwayNotMem.lean#L66-L114

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.tan_prime_uniq {w : sp (R₀ := S) (DualNumber S) ⟶ G} (hw : TanS w)
    (h1 : spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ w = 1) :
    ∃ q ∈ p.primeCompl, spMap (scaleS (S := S) q) ≫ w = 1 := by sorry
