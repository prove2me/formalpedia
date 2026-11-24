-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Fr_IsFr_ext
-- name    : PositivityTheory.ThKCT.Fr.IsFr.ext
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:46:58.651863+00:00
-- url     : https://prove2.me/theorems/c1adcf08-2d6c-416c-aa8a-0ee0328df6ce
-- title:
--   Is Fr: ext
-- statement:
--   The Is Fr construction uses the ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/ColsOfMul.lean#L204-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/ColsOfMul.lean#L204-L218

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

theorem PositivityTheory.ThKCT.Fr.IsFr.ext (h : IsFr c ε J J₁ ι x y A') {m m' : Matrix d d R} (h1 : m *ᵥ x = m' *ᵥ x) (h2 : m *ᵥ y = m' *ᵥ y)
    (h3 : m * ι = m' * ι) : m = m' := by sorry
