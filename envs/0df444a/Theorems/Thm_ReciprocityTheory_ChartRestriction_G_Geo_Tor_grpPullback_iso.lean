-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.grpPullback_iso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:40.386991+00:00
-- url     : https://prove2.me/theorems/772321a4-b0a0-4e8a-868b-80ba7b22504f
-- title:
--   Tor: grp Pullback iso
-- statement:
--   The Tor construction uses the grp Pullback iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/BCTools.lean#L44-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/BCTools.lean#L44-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {S S' : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.grpPullback_iso {G : Over S} {G₁ G₂ : Over S'} [GrpObj G] [GrpObj G₁] [GrpObj G₂] {f : S' ⟶ S}
    {φ₁ : G₁.left ⟶ G.left} {φ₂ : G₂.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f φ₁) (h₂ : IsGrpPullback G₂ G f φ₂) :
    ∃ e : G₁ ≅ G₂, IsMonHom e.hom ∧ e.hom.left ≫ φ₂ = φ₁ := by sorry
