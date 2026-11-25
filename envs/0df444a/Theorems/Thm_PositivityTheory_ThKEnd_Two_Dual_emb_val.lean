-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_Dual_emb_val
-- name    : PositivityTheory.ThKEnd.Two.Dual.emb_val
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:15.868721+00:00
-- url     : https://prove2.me/theorems/03fcb522-c9a8-5880-a36f-fa2a3fbf06e3
-- title:
--   Dual: emb val
-- statement:
--   The Dual construction uses the emb val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/EmbMMul.lean#L124-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/EmbMMul.lean#L124-L124

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

theorem PositivityTheory.ThKEnd.Two.Dual.emb_val (h : Dual c J X Y) (g : GL k R) : (h.emb g).1.1 = embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ := by sorry
