-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_away_not_mem
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.exists_away_not_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:56:47.54865+00:00
-- url     : https://prove2.me/theorems/22a93675-46a8-4600-ba2c-e91e92ee0127
-- title:
--   Chart: exists away not mem
-- statement:
--   The Chart construction uses the exists away not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ExistsAwayNotMem.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ExistsAwayNotMem.lean#L16-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PairCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsAwayNotMem
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory

theorem ReciprocityTheory.ChartRestriction.G.Chart.exists_away_not_mem {S : Type} [CommRing S] {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    (p : Ideal S) [p.IsPrime] : ∃ k, s k ∉ p := by sorry
