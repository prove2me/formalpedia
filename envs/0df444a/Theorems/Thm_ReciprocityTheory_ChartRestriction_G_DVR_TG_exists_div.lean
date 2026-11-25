-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_exists_div
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.exists_div
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:11:05.821625+00:00
-- url     : https://prove2.me/theorems/de676377-af8d-558b-944e-45baa9f28da7
-- title:
--   TG: exists div
-- statement:
--   The TG construction uses the exists div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenThick.lean#L33-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenThick.lean#L33-L72

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.exists_div {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] {a : R} (ha : a ≠ 0)
    {J : Ideal R} (hJ : J ≤ Ideal.span {a})
    (V : X.Opens) (x : Γ(X, V)) (hx : (pullback.fst p (tq J)).app V x = 0) :
    ∃ g : Γ(X, V), x = toW p V a * g := by sorry
