-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_Dual_emb_cont
-- name    : PositivityTheory.ThKEnd.Two.Dual.emb_cont
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:59:47.62952+00:00
-- url     : https://prove2.me/theorems/44fdc564-15e7-51b1-ad0d-a4b4f3044d32
-- title:
--   Dual: emb cont
-- statement:
--   The Dual construction uses the emb cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/EmbMMul.lean#L126-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/EmbMMul.lean#L126-L139

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

theorem PositivityTheory.ThKEnd.Two.Dual.emb_cont [TopologicalSpace R] [IsTopologicalRing R] (h : Dual c J X Y) (hc : Continuous c) : Continuous h.emb := by sorry
