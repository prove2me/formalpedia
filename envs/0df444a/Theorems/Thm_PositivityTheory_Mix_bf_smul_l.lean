-- Prove2me | Theorems.Thm_PositivityTheory_Mix_bf_smul_l
-- name    : PositivityTheory.Mix.bf_smul_l
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:21:42.08583+00:00
-- url     : https://prove2.me/theorems/a64d679b-b97f-40da-ae7e-de564b9b4351
-- title:
--   Mix: bf smul l
-- statement:
--   The Mix construction uses the bf smul l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/MixedModels/PlaneGen.lean#L17-L18

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

theorem PositivityTheory.Mix.bf_smul_l (a : R) (u v) : bf c J (a • u) v = a * bf c J u v := by sorry
