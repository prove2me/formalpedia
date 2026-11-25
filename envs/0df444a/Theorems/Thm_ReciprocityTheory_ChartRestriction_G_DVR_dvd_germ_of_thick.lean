-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_dvd_germ_of_thick
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.dvd_germ_of_thick
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:40.415472+00:00
-- url     : https://prove2.me/theorems/b8f4ad96-c20c-4330-bd7f-81da4b15e8d5
-- title:
--   DVR: dvd germ of thick
-- statement:
--   The DVR construction uses the dvd germ of thick property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThickKer.lean#L114-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThickKer.lean#L114-L173

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThickKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {V : Type} [CommRing V] {X : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.DVR.dvd_germ_of_thick (p : X ⟶ Sp V) (J : Ideal V) {r : V} (hJ : J ≤ Ideal.span {r}) {W : X.Opens}
    (a : Γ(X, W)) (x' : ↑(pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hx : pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' ∈ W)
    (h : cst (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫ p) x' r ∣
      gs (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) x' W a) :
    cst p (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x') r ∣
      gs (𝟙 X) (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x') W a := by sorry
