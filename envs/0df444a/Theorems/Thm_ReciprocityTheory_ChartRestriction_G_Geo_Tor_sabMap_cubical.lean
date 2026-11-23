-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabMap_cubical
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabMap_cubical
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:20.252214+00:00
-- url     : https://prove2.me/theorems/1952fdb0-10ca-4844-a298-9fafd28d9449
-- title:
--   Tor: sab Map cubical
-- statement:
--   The Tor construction uses the sab Map cubical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabMapCubical.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabMapCubical.lean#L14-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabMapCubical
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
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabMap_cubical {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f : S' ⟶ S} (m₁ : SABMap t₁ t f)
    (m₂ : SABMap t₂ t f) (ψ : t₁.G ≅ t₂.G) [IsMonHom ψ.hom] (hφ : ψ.hom.left ≫ m₂.φ = m₁.φ) :
    (CubeMap.ofHom ψ.hom).IsPullCubical t₁.cub t₂.cub := by sorry
