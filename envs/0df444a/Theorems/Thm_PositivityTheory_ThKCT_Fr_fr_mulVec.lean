-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Fr_fr_mulVec
-- name    : PositivityTheory.ThKCT.Fr.fr_mulVec
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:47:07.801434+00:00
-- url     : https://prove2.me/theorems/b76675ba-b858-4048-ae0b-e88d3dfb08ad
-- title:
--   Fr: fr mul Vec
-- statement:
--   The Fr construction uses the fr mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/ColsOfMul.lean#L221-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/ColsOfMul.lean#L221-L223

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
omit [DecidableEq d] [DecidableEq e]

theorem PositivityTheory.ThKCT.Fr.fr_mulVec (u : e → R) (s t : R) : fr ι x y *ᵥ Sum.elim u ![s, t] = ι *ᵥ u + s • x + t • y := by sorry
