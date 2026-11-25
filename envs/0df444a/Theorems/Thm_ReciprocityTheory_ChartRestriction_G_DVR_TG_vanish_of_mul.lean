-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_vanish_of_mul
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.vanish_of_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:11:44.835323+00:00
-- url     : https://prove2.me/theorems/d9951e1a-6206-4c3f-a61b-186cdd86558d
-- title:
--   TG: vanish of mul
-- statement:
--   The TG construction uses the vanish of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenThick.lean#L114-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenThick.lean#L114-L180

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenThick
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section
variable {R : Type} [CommRing R]
variable [IsDomain R]
set_option maxHeartbeats 400000

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.vanish_of_mul {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] {a : R} (ha : a ≠ 0)
    (e : ℕ) {J₁ J₂ : Ideal R} (h1 : J₁ ≤ Ideal.span {a ^ (e + 2)}) (h2 : a ^ (e + 1) ∈ J₂)
    (ι : pullback p (tq J₂) ⟶ pullback p (tq J₁)) (hι : ι ≫ pullback.fst p (tq J₁) = pullback.fst p (tq J₂))
    (V : (pullback p (tq J₁)).Opens) (y : Γ(pullback p (tq J₁), V))
    (hy : toW (pullback.fst p (tq J₁) ≫ p) V a * y = 0) :
    (ι.app V) y = 0 := by sorry
