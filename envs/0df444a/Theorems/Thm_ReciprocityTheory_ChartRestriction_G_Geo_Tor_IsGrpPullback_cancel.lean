-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_cancel
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback.cancel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:16.839532+00:00
-- url     : https://prove2.me/theorems/da62d4df-97fa-4568-9748-72df3b130210
-- title:
--   Is Grp Pullback: cancel
-- statement:
--   The Is Grp Pullback construction uses the cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabComp.lean#L39-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabComp.lean#L39-L56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback.cancel {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (h : IsGrpPullback G' G f φ) (n : IsGrpPullback G'' G (g ≫ f) (φ' ≫ φ)) (w : φ' ≫ G'.hom = G''.hom ≫ g) :
    IsGrpPullback G'' G' g φ' := by sorry
