-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_iso_of_hf
-- name    : PositivityTheory.ThKG.Tow.Levi.iso_of_hf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:24.81227+00:00
-- url     : https://prove2.me/theorems/817e2bfb-b4a0-43e8-b8f5-9e6e72b1f50b
-- title:
--   Levi: iso of hf
-- statement:
--   The Levi construction uses the iso of hf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/ExistsRefl.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/ExistsRefl.lean#L25-L29

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

theorem PositivityTheory.ThKG.Tow.Levi.iso_of_hf {g : Matrix n n ℂ} (h : ∀ x y, hf M (g *ᵥ x) (g *ᵥ y) = hf M x y) : gᵀ * M * g.map star = M := by sorry
