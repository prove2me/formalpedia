-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_pgen_cancel
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Tri.pgen_cancel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:15.964857+00:00
-- url     : https://prove2.me/theorems/1585c843-3946-489d-b9ef-f6807e75b9d9
-- title:
--   Tri: pgen cancel
-- statement:
--   The Tri construction uses the pgen cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean#L341-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean#L341-L353

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
variable {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.Tri.pgen_cancel (T : Tri w w' w'') (hL : L.IsLB) (hw : PGen w) (hw'' : PGen w'') : PGen w' := by sorry
