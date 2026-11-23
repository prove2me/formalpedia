-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_exists_gen_move
-- name    : ReciprocityTheory.ChartRestriction.G.H1.exists_gen_move
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:28.242716+00:00
-- url     : https://prove2.me/theorems/0bdb6c41-43b9-4fab-8b90-2baf80916ea6
-- title:
--   H1: exists gen move
-- statement:
--   The H1 construction uses the exists gen move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/GenMove.lean#L14-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/GenMove.lean#L14-L84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem ReciprocityTheory.ChartRestriction.G.H1.exists_gen_move (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (h : Y' ⟶ Y)
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ PMaps w φ' φ ε a t h := by sorry
