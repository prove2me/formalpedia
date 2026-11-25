-- Prove2me | Theorems.Thm_PositivityTheory_Mix_bf_add_r
-- name    : PositivityTheory.Mix.bf_add_r
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:42.239428+00:00
-- url     : https://prove2.me/theorems/c2ee4028-ee4d-4452-83a6-0fc5bb038352
-- title:
--   Mix: bf add r
-- statement:
--   The Mix construction uses the bf add r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L19-L23

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

theorem PositivityTheory.Mix.bf_add_r (u v v') : bf c J u (v + v') = bf c J u v + bf c J u v' := by sorry
