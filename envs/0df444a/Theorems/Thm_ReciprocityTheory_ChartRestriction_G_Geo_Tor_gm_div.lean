-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:22.526457+00:00
-- url     : https://prove2.me/theorems/1cd01f7a-8e74-4d91-babb-55dd20e35139
-- title:
--   Tor: gm div
-- statement:
--   The Tor construction uses the gm div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabPull.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabPull.lean#L24-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
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
variable {X X' Y Y' : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_div {Z : Scheme.{0}} (A B : LB Y) (r : Z ⟶ Y) (z : Z) (p q : B.ι × A.ι)
    (hm : r z ∈ B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2)) :
    gm r z (B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2)) ((LB.div B A).g p q) =
      gm r z _ (B.g p.1 q.1) * (gm r z _ (A.g p.2 q.2))⁻¹ := by sorry
