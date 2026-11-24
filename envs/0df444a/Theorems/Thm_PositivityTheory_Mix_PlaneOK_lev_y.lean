-- Prove2me | Theorems.Thm_PositivityTheory_Mix_PlaneOK_lev_y
-- name    : PositivityTheory.Mix.PlaneOK.lev_y
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:45:56.36093+00:00
-- url     : https://prove2.me/theorems/e433f779-8076-41db-955f-af54ac74158a
-- title:
--   Plane OK: lev y
-- statement:
--   The Plane OK construction uses the lev y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L107-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L107-L113

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

theorem PositivityTheory.Mix.PlaneOK.lev_y (t s : R) : lev c J ε x y t s *ᵥ y = s • y := by sorry
