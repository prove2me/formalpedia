-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_exists_refl
-- name    : PositivityTheory.ThKG.Tow.Levi.exists_refl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:04:59.94193+00:00
-- url     : https://prove2.me/theorems/d24d77b2-fce3-4185-a359-d601568364e9
-- title:
--   Levi: exists refl
-- statement:
--   The Levi construction uses the exists refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/ExistsRefl.lean#L39-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/ExistsRefl.lean#L39-L88

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

theorem PositivityTheory.ThKG.Tow.Levi.exists_refl (hM : ∀ i j, star (M j i) = M i j) (h1 : θ * θ = 1) (h2 : θᵀ * M * θ.map star = M)
    (h3 : ∀ x : n → ℂ, x ≠ 0 → 0 < (hf M (θ *ᵥ x) x).re) {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {u u' : n → ℂ}
    (hu : θ *ᵥ u = ε • u) (hu' : θ *ᵥ u' = ε • u') (e : hf M u u = hf M u' u') :
    ∃ κ : Matrix n n ℂ, κᵀ * M * κ.map star = M ∧ Commute κ θ ∧ κ *ᵥ u = u' ∧ ∀ z, θ *ᵥ z = -ε • z → κ *ᵥ z = z := by sorry
