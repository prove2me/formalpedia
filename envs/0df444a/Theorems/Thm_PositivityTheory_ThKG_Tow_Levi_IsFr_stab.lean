-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_IsFr_stab
-- name    : PositivityTheory.ThKG.Tow.Levi.IsFr.stab
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:31.649938+00:00
-- url     : https://prove2.me/theorems/fbf622e6-0460-48cd-b29c-865f4b5b3582
-- title:
--   Is Fr: stab
-- statement:
--   The Is Fr construction uses the stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/LeviAlg.lean#L107-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/LeviAlg.lean#L107-L140

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_TowerModels_LeviAlg
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
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}

theorem PositivityTheory.ThKG.Tow.Levi.IsFr.stab (h : IsFr c J J₁ ι x y) {t t' : R} (ht : t * t' = 1) {p : Matrix d d R}
    (hp : pᵀ * J * p.map c = J) (hx : p *ᵥ x = t • x) :
    ∃ (g : Matrix e e R) (α : e → R), gᵀ * J₁ * g.map c = J₁ ∧ ∀ z, p *ᵥ (ι *ᵥ z) = ι *ᵥ (g *ᵥ z) + (α ⬝ᵥ z) • x := by sorry
