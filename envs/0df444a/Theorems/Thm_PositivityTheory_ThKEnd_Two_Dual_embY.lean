-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_Dual_embY
-- name    : PositivityTheory.ThKEnd.Two.Dual.embY
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:59:52.768066+00:00
-- url     : https://prove2.me/theorems/1d594d2b-0a84-519a-9a98-44f7c51d4a76
-- title:
--   Dual: emb Y
-- statement:
--   The Dual construction uses the emb Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/EmbMMul.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/EmbMMul.lean#L68-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_EmbMMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open Matrix GlobalTheory.WeilM
variable {S R d k : Type} [CommRing S] [CommRing R] [Algebra S R] [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
variable {c : R →ₐ[S] R} {J : Matrix d d R} {X Y : Matrix d k R}

theorem PositivityTheory.ThKEnd.Two.Dual.embY (h : Dual c J X Y) (g g' : Matrix k k R) : embM c J X Y g g' * Y = Y * g' := by sorry
