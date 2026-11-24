-- Prove2me | Theorems.Thm_PositivityTheory_Mix_PlaneOK_lev_apply
-- name    : PositivityTheory.Mix.PlaneOK.lev_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:03.538038+00:00
-- url     : https://prove2.me/theorems/0d8317e3-49b3-48d0-94e8-576c66db3c1d
-- title:
--   Plane OK: lev apply
-- statement:
--   The Plane OK construction uses the lev apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L92-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L92-L100

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_MixedModels_PlaneGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Mix
open Matrix
variable {R : Type} [CommRing R] {n k : ℕ}
variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R}
open PositivityTheory.Mix.PlaneOK
variable {ε : R} {x y : Fin n → R} {ι : Matrix (Fin n) (Fin k) R} (h : PlaneOK c J ε x y ι)
include h
omit h

theorem PositivityTheory.Mix.PlaneOK.lev_apply (t s : R) (v) : lev c J ε x y t s *ᵥ v = v + ((t - 1) * bf c J v y) • x + ((s - 1) * ε * bf c J v x) • y := by sorry
