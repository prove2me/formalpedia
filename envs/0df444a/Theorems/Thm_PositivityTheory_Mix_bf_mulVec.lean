-- Prove2me | Theorems.Thm_PositivityTheory_Mix_bf_mulVec
-- name    : PositivityTheory.Mix.bf_mulVec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:52:05.658654+00:00
-- url     : https://prove2.me/theorems/448361d2-8265-44c8-9cba-5e093c8f42fb
-- title:
--   Mix: bf mul Vec
-- statement:
--   The Mix construction uses the bf mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L30-L35

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

theorem PositivityTheory.Mix.bf_mulVec (M : Matrix (Fin n) (Fin n) R) (u v) : bf c J (M *ᵥ u) (M *ᵥ v) = bf c (Mᵀ * J * M.map c) u v := by sorry
