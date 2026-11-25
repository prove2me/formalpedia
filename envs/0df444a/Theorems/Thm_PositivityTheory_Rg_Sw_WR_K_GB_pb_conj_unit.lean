-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_conj_unit
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.pb_conj_unit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:07.888569+00:00
-- url     : https://prove2.me/theorems/512ce4ab-e9ca-4e4a-a9b1-e158633c80e5
-- title:
--   GB: pb conj unit
-- statement:
--   The GB construction uses the pb conj unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBBound.lean#L233-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBBound.lean#L233-L239

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.K.GB.pb_conj_unit (Y k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : IsUnit Y.det) :
    IsUnit (k * Y * kᴴ).det := by sorry
