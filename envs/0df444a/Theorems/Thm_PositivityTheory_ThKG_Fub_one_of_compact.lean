-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Fub_one_of_compact
-- name    : PositivityTheory.ThKG.Fub.one_of_compact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:00:19.812553+00:00
-- url     : https://prove2.me/theorems/7ae1aa67-3d07-59b8-984d-680474713e33
-- title:
--   Fub: one of compact
-- statement:
--   The Fub construction uses the one of compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubTate.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubTate.lean#L9-L22

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

theorem PositivityTheory.ThKG.Fub.one_of_compact {G : Type} [Group G] [TopologicalSpace G] (f : G →* NNReal) (hf : Continuous f) {K : Set G} (hK : IsCompact K)
    {x : G} (hx : ∀ n : ℤ, x ^ n ∈ K) : f x = 1 := by sorry
