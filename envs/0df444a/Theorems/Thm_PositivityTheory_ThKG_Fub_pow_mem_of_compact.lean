-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Fub_pow_mem_of_compact
-- name    : PositivityTheory.ThKG.Fub.pow_mem_of_compact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:00:40.336804+00:00
-- url     : https://prove2.me/theorems/8f24df6e-d488-421b-a907-b61abc8e3f43
-- title:
--   Fub: pow mem of compact
-- statement:
--   The Fub construction uses the pow mem of compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubTate.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubTate.lean#L49-L57

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubTate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Fub
open MeasureTheory Topology Filter

theorem PositivityTheory.ThKG.Fub.pow_mem_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G))
    {K : Set G} (hK : IsCompact K) {x : G} (hx : ∀ n : ℕ, x ^ n ∈ K) : ∃ k : ℕ, 0 < k ∧ x ^ k ∈ U := by sorry
