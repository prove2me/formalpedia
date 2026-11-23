-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isMonHom_of_mul
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:14.771432+00:00
-- url     : https://prove2.me/theorems/bf56e221-f5d3-4652-9c0a-473d4baa9cd6
-- title:
--   Tor: is Mon Hom of mul
-- statement:
--   The Tor construction uses the is Mon Hom of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsMonHomOfMul.lean#L412-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsMonHomOfMul.lean#L412-L425

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂] (e : G₁ ⟶ G₂)
    (mul : ∀ (T : Over S) (x y : T ⟶ G₁), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) : IsMonHom e := by sorry
