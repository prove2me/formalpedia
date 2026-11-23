-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div_g
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_div_g
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:46:11.801497+00:00
-- url     : https://prove2.me/theorems/b2a1628c-ffff-4384-b551-1ce839a08f3a
-- title:
--   Tor: gm div g
-- statement:
--   The Tor construction uses the gm div g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean#L117-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean#L117-L133

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}}
variable {X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_div_g (f : Y ⟶ X') (y : Y) (j j' : L.ι) (k k' : L'.ι) (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j')
    (hk : f y ∈ L'.U k) (hk' : f y ∈ L'.U k') :
    gm f y ((L.pull F).U (fun _ => j) ⊓ L'.U k ⊓ ((L.pull F).U (fun _ => j') ⊓ L'.U k'))
      ((LB.div (L.pull F) L').g (fun _ => j, k) (fun _ => j', k')) =
      gm (f ≫ F) y _ (L.g j j') * (gm f y _ (L'.g k k'))⁻¹ := by sorry
