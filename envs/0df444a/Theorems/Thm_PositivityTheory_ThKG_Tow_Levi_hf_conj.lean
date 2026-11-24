-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_hf_conj
-- name    : PositivityTheory.ThKG.Tow.Levi.hf_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:21.459408+00:00
-- url     : https://prove2.me/theorems/8828dd9d-b71c-484d-bb95-2eef0a2be4ed
-- title:
--   Levi: hf conj
-- statement:
--   The Levi construction uses the hf conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/ExistsRefl.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/ExistsRefl.lean#L32-L37

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_TowerModels_ExistsRefl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.ThKG.Tow.Levi
open Matrix
variable {n : Type} [Fintype n] [DecidableEq n]
variable {M θ : Matrix n n ℂ}
omit [DecidableEq n]

theorem PositivityTheory.ThKG.Tow.Levi.hf_conj (hM : ∀ i j, star (M j i) = M i j) (x y : n → ℂ) : starRingEnd ℂ (hf M x y) = hf M y x := by sorry
