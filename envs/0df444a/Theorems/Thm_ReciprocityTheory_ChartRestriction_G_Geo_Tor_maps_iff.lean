-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.maps_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:57.269641+00:00
-- url     : https://prove2.me/theorems/4f2a438a-9318-49d8-9621-fd3db2b7e102
-- title:
--   Tor: maps iff
-- statement:
--   The Tor construction uses the maps iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean#L183-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean#L183-L205

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.maps_iff (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} (φ' : K → (Y' ⟶ X'))
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)) (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (b : LB.Gen (LB.LinComb (L.pull F) φ' ε))
    (hle : ∀ j : K → PUnit → L.ι, LB.wchart (L.pull F) φ' j ≤ h ⁻¹ᵁ LB.wchart L φ (fun k => j k PUnit.unit))
    (hb : ∀ j, b.s j = res (hle j) (pullU h _ (t.s (fun k => j k PUnit.unit)))) :
    LB.Gen.Maps (LB.linCombIso w φ' ε) a b ↔ PMaps w φ' φ ε a t h := by sorry
