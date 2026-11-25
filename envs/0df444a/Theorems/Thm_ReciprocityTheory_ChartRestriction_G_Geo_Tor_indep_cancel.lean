-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_indep_cancel
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.indep_cancel
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:24:36.634165+00:00
-- url     : https://prove2.me/theorems/c08d0da4-44f6-4709-8e06-b261e022e6d4
-- title:
--   Tor: indep cancel
-- statement:
--   The Tor construction uses the indep cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean#L232-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean#L232-L240

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
variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.indep_cancel (w : LB.Iso L' (L.pull F)) (w'' : LB.Iso L'' (L.pull (F' ≫ F))) (hw : PGen w) (hw'' : PGen w'')
    (hL' : L'.IsLB) (hL'' : L''.IsLB) {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y) (j j' : L.ι) (i : L'.ι) (k : L''.ι)
    (hj : F (F' (f y)) ∈ L.U j) (hj' : F (F' (f y)) ∈ L.U j') (hi : F' (f y) ∈ L'.U i) (hk : f y ∈ L''.U k) :
    (gw w (f ≫ F') y j i)⁻¹ * gw w'' f y j k = (gw w (f ≫ F') y j' i)⁻¹ * gw w'' f y j' k := by sorry
