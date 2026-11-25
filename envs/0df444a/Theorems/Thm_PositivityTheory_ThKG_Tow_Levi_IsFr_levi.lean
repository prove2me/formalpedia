-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_IsFr_levi
-- name    : PositivityTheory.ThKG.Tow.Levi.IsFr.levi
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:41.063987+00:00
-- url     : https://prove2.me/theorems/e612fb92-01ca-4468-b0d3-552cc27063b2
-- title:
--   Is Fr: levi
-- statement:
--   The Is Fr construction uses the levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/LeviAlg.lean#L67-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/LeviAlg.lean#L67-L105

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

theorem PositivityTheory.ThKG.Tow.Levi.IsFr.levi (h : IsFr c J J₁ ι x y) (hcc : ∀ a, c (c a) = a) {t t' : R} (ht : t * t' = 1) {g g' : Matrix e e R}
    (hg' : g * g' = 1) (hg : gᵀ * J₁ * g.map c = J₁) :
    ∃ m m' : Matrix d d R, m * m' = 1 ∧ mᵀ * J * m.map c = J ∧ m *ᵥ x = t • x ∧ m *ᵥ y = c t' • y ∧ m * ι = ι * g := by sorry
