-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_dom_iff
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.dom_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:24:45.424702+00:00
-- url     : https://prove2.me/theorems/6c7da37f-82dc-4211-af6f-58bbddde91fb
-- title:
--   Tor: dom iff
-- statement:
--   The Tor construction uses the dom iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/OneArc.lean#L81-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/OneArc.lean#L81-L103

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.dom_iff {O₀ O : Type} [CommRing O₀] [CommRing O] {β₀ : O₀ →+* c.F} {β : O →+* c.F} {b : O₀ →+* O}
    {Yg : Model Xo c β₀} {Y : Model Xo c β} {f : pullback Yg.s (spMap b) ⟶ Y.X} {t₁ : SAB H (pullback Yg.s (spMap b))}
    (m₁ : SABMap t₁ Yg.t (pullback.fst _ _)) (m₂ : SABMap t₁ Y.t f)
    (hc : ∀ (T : Scheme.{0}) (g : T ⟶ t₁.G.left) (g₁ : T ⟶ Yg.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Yg.m.φ → g₁ ≫ Yg.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ →
      g₁ ≫ Yg.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom → g ≫ m₂.φ = g₂ ≫ Y.m.φ)
    (aF : Xo.XF c ⟶ pullback Yg.s (spMap b)) (haF : aF ≫ pullback.fst _ _ = Yg.j) {T : Scheme.{0}}
    (g : T ⟶ t₁.G.left) (gg : T ⟶ Yg.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left)
    (h₀ : gg ≫ Yg.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ) (h₁ : gg ≫ Yg.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom)
    (hb : g ≫ t₁.G.hom = gg ≫ Yg.oF.t.G.hom ≫ aF) : g ≫ m₁.φ = gg ≫ Yg.m.φ ↔ g ≫ m₂.φ = g₂ ≫ Y.m.φ := by sorry
