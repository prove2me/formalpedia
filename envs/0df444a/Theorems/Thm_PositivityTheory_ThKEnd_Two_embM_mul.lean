-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_embM_mul
-- name    : PositivityTheory.ThKEnd.Two.embM_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:49.271546+00:00
-- url     : https://prove2.me/theorems/802c10f0-382b-49af-9114-1ed99c489967
-- title:
--   Two: emb M mul
-- statement:
--   The Two construction uses the emb M mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/EmbMMul.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/EmbMMul.lean#L59-L61

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

theorem PositivityTheory.ThKEnd.Two.embM_mul {e : Type} (g g' : Matrix k k R) (T : Matrix d e R) :
    embM c J X Y g g' * T = T + X * (g - 1) * (Tᵀ * J * Y.map c)ᵀ - Y * (g' - 1) * (Tᵀ * J * X.map c)ᵀ := by sorry
