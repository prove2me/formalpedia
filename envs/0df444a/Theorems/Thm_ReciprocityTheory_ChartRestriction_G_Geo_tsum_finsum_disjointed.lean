-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_tsum_finsum_disjointed
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.tsum_finsum_disjointed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:25:31.292328+00:00
-- url     : https://prove2.me/theorems/399b89cf-b662-41d8-ae37-df8692630769
-- title:
--   Geo: tsum finsum disjointed
-- statement:
--   The Geo construction uses the tsum finsum disjointed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeG.lean#L141-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeG.lean#L141-L171

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Set Filter Topology Function
variable {e : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.tsum_finsum_disjointed {α : Type*} {D : ℕ → Set α} (hd : Pairwise (Disjoint on D))
    {O : Set α} (hU : ⋃ n, D n = O) {G : Set α} (hG : (O ∩ G).Finite) (f : α → ℝ) :
    ∑' n, ∑ᶠ u ∈ D n ∩ G, f u = ∑ᶠ u ∈ O ∩ G, f u := by sorry
