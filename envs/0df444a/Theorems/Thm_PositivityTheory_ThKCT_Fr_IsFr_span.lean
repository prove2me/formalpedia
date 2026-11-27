-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Fr_IsFr_span
-- name    : PositivityTheory.ThKCT.Fr.IsFr.span
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:58:54.403691+00:00
-- url     : https://prove2.me/theorems/8b212376-0e08-5432-97cd-ea0d69c44be0
-- title:
--   Is Fr: span
-- statement:
--   The Is Fr construction uses the span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/ColsOfMul.lean#L225-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/ColsOfMul.lean#L225-L234

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

theorem PositivityTheory.ThKCT.Fr.IsFr.span (h : IsFr c ε J J₁ ι x y A') (z : d → R) : ∃ (u : e → R) (s t : R), z = ι *ᵥ u + s • x + t • y := by sorry
