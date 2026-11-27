-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_exists_move
-- name    : PositivityTheory.ThKG.Tow.Levi.exists_move
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:01.518828+00:00
-- url     : https://prove2.me/theorems/a8d6ef2b-b314-4a6d-98bc-08d7fbd9a00e
-- title:
--   Levi: exists move
-- statement:
--   The Levi construction uses the exists move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/ExistsRefl.lean#L90-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/ExistsRefl.lean#L90-L123

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

theorem PositivityTheory.ThKG.Tow.Levi.exists_move (hM : ∀ i j, star (M j i) = M i j) (h1 : θ * θ = 1) (h2 : θᵀ * M * θ.map star = M)
    (h3 : ∀ x : n → ℂ, x ≠ 0 → 0 < (hf M (θ *ᵥ x) x).re) {v v' : n → ℂ} (hv : v ≠ 0) (hv' : v' ≠ 0)
    (e : hf M v v = 0) (e' : hf M v' v' = 0) :
    ∃ (κ : Matrix n n ℂ) (t : ℂ), t ≠ 0 ∧ κᵀ * M * κ.map star = M ∧ Commute κ θ ∧ κ *ᵥ v = t • v' := by sorry
