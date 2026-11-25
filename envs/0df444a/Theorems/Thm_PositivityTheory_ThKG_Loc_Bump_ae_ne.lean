-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_ae_ne
-- name    : PositivityTheory.ThKG.Loc.Bump.ae_ne
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:04:17.493684+00:00
-- url     : https://prove2.me/theorems/004fe503-a11f-5769-9641-e92a61e1f861
-- title:
--   Bump: ae ne
-- statement:
--   The Bump construction uses the ae ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/DictHaar.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/DictHaar.lean#L32-L36

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

theorem PositivityTheory.ThKG.Loc.Bump.ae_ne : ∀ᵐ c : ι → ℂ, ∀ w, c w ≠ 0 := by sorry
