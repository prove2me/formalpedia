-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_map_mul_vol
-- name    : PositivityTheory.ThKG.Loc.Bump.map_mul_vol
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:04:25.66674+00:00
-- url     : https://prove2.me/theorems/334d7ef6-d981-5aa5-b887-e3b8e080c7c3
-- title:
--   Bump: map mul vol
-- statement:
--   The Bump construction uses the map mul vol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/DictHaar.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/DictHaar.lean#L12-L24

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_DictHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
variable {ι : Type} [Fintype ι]

theorem PositivityTheory.ThKG.Loc.Bump.map_mul_vol (s : ι → ℂ) (hs : ∀ w, s w ≠ 0) :
    Measure.map (fun c : ι → ℂ => s * c) volume = ENNReal.ofReal (∏ w, ‖s w‖ ^ 2)⁻¹ • volume := by sorry
