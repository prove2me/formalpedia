-- Prove2me | Theorems.Thm_PositivityTheory_Mix_PlaneOK_lev_mul
-- name    : PositivityTheory.Mix.PlaneOK.lev_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:25.682883+00:00
-- url     : https://prove2.me/theorems/96306ccc-b4f6-422a-9399-5fd428a26168
-- title:
--   Plane OK: lev mul
-- statement:
--   The Plane OK construction uses the lev mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L118-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L118-L123

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

theorem PositivityTheory.Mix.PlaneOK.lev_mul {t t' s s' : R} (h1 : t * t' = 1) (h2 : s * s' = 1) : lev c J ε x y t s * lev c J ε x y t' s' = 1 := by sorry
