-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback.congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:55.067302+00:00
-- url     : https://prove2.me/theorems/ba228dcf-d30a-4822-a1c7-214ec8cbefbc
-- title:
--   Is Grp Pullback: congr
-- statement:
--   The Is Grp Pullback construction uses the congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/BCTools.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/BCTools.lean#L30-L33

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback.congr {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f f' : S' ⟶ S} {φ φ' : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (e : f = f') (e' : φ = φ') : IsGrpPullback G' G f' φ' := by sorry
