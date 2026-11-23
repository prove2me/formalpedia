-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabPull
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabPull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:16.209955+00:00
-- url     : https://prove2.me/theorems/1d0705a3-2b4d-48ba-91f1-75c791380c6c
-- title:
--   Tor: sab Pull
-- statement:
--   The Tor construction uses the sab Pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabPull.lean#L155-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabPull.lean#L155-L184

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabPull (hC : Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ (PP' : RigLB ((Over.pullback f).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
      (m : SABMap ⟨(Over.pullback f).obj t.G, IsSemiAbelian.pullback f t.G t.semi, OAct.pullback f t.G t.act, PP', cub,
        sym, adj, prim⟩ t f), m.φ = pullback.fst t.G.hom f := by sorry
