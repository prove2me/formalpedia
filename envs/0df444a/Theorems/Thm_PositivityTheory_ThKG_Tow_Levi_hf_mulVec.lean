-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_hf_mulVec
-- name    : PositivityTheory.ThKG.Tow.Levi.hf_mulVec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:21.616372+00:00
-- url     : https://prove2.me/theorems/d59e9363-8c2b-4d6d-b708-0a72beef3550
-- title:
--   Levi: hf mul Vec
-- statement:
--   The Levi construction uses the hf mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/ExistsRefl.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/ExistsRefl.lean#L21-L23

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

theorem PositivityTheory.ThKG.Tow.Levi.hf_mulVec (g : Matrix n n ℂ) (x y : n → ℂ) : hf M (g *ᵥ x) (g *ᵥ y) = hf (gᵀ * M * g.map star) x y := by sorry
