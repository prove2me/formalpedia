-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Fr_IsFr_stab
-- name    : PositivityTheory.ThKCT.Fr.IsFr.stab
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:59:18.221509+00:00
-- url     : https://prove2.me/theorems/970960ef-e1e3-52cb-9fc9-893c5e424c18
-- title:
--   Is Fr: stab
-- statement:
--   The Is Fr construction uses the stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/ColsOfMul.lean#L169-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/ColsOfMul.lean#L169-L202

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_ColsOfMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Fr
open Matrix
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {ε : R} {A' : Matrix (e ⊕ Fin 2) d R} {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}

theorem PositivityTheory.ThKCT.Fr.IsFr.stab (h : IsFr c ε J J₁ ι x y A') {t t' : R} (ht : t * t' = 1) {p : Matrix d d R}
    (hp : pᵀ * J * p.map c = J) (hx : p *ᵥ x = t • x) :
    ∃ (g : Matrix e e R) (α : e → R), g = (A' * p * fr ι x y).toBlocks₁₁ ∧ gᵀ * J₁ * g.map c = J₁ ∧ ∀ z, p *ᵥ (ι *ᵥ z) = ι *ᵥ (g *ᵥ z) + (α ⬝ᵥ z) • x := by sorry
