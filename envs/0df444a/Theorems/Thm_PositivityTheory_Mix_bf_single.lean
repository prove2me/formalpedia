-- Prove2me | Theorems.Thm_PositivityTheory_Mix_bf_single
-- name    : PositivityTheory.Mix.bf_single
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:51:54.200083+00:00
-- url     : https://prove2.me/theorems/490cd717-f54d-52d7-992f-5657c2ebaa30
-- title:
--   Mix: bf single
-- statement:
--   The Mix construction uses the bf single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L37-L45

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

theorem PositivityTheory.Mix.bf_single (i j : Fin n) : bf c J (Pi.single i 1) (Pi.single j 1) = J i j := by sorry
