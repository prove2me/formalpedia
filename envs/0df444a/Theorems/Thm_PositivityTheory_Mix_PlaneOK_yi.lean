-- Prove2me | Theorems.Thm_PositivityTheory_Mix_PlaneOK_yi
-- name    : PositivityTheory.Mix.PlaneOK.yi
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:07.967842+00:00
-- url     : https://prove2.me/theorems/c897f650-0a28-50ff-b5c8-65d5d1ca2a35
-- title:
--   Plane OK: yi
-- statement:
--   The Plane OK construction uses the yi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L74-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L74-L74

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

theorem PositivityTheory.Mix.PlaneOK.yi (z) : bf c J y (ι *ᵥ z) = 0 := by sorry
