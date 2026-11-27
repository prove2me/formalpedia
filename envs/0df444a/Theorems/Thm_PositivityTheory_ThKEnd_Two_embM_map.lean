-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_embM_map
-- name    : PositivityTheory.ThKEnd.Two.embM_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:00:27.110066+00:00
-- url     : https://prove2.me/theorems/ccd570ba-f936-4584-a9f0-380a033c015e
-- title:
--   Two: emb M map
-- statement:
--   The Two construction uses the emb M map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/EmbMMul.lean#L141-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/EmbMMul.lean#L141-L146

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

theorem PositivityTheory.ThKEnd.Two.embM_map {S' R' : Type} [CommRing S'] [CommRing R'] [Algebra S' R'] {c' : R' →ₐ[S'] R'} (f : R →+* R')
    (hf : ∀ a, f (c a) = c' (f a)) (g g' : Matrix k k R) :
    (embM c J X Y g g').map f = embM c' (J.map f) (X.map f) (Y.map f) (g.map f) (g'.map f) := by sorry
