-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cancel
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_cancel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:06.966304+00:00
-- url     : https://prove2.me/theorems/79edea67-51c0-473b-8204-b737ed74d115
-- title:
--   Tor: exists cancel
-- statement:
--   The Tor construction uses the exists cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean#L283-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean#L283-L325

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_cancel (hL : L.IsLB) (w : LB.Iso L' (L.pull F)) (w'' : LB.Iso L'' (L.pull (F' ≫ F))) (hw : PGen w)
    (hw'' : PGen w'') (hL' : L'.IsLB) (hL'' : L''.IsLB) :
    ∃ w' : LB.Iso L'' (L'.pull F'), Tri w w' w'' := by sorry
