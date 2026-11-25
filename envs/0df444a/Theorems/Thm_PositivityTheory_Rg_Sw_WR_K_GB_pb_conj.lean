-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_conj
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.pb_conj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:49:49.863304+00:00
-- url     : https://prove2.me/theorems/b6ac2242-fc52-4378-99f9-136b59823cf6
-- title:
--   GB: pb conj
-- statement:
--   The GB construction uses the pb conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBBound.lean#L223-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBBound.lean#L223-L225

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

theorem PositivityTheory.Rg.Sw.WR.K.GB.pb_conj (c : ℂ) (k b : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    1 - c • (k * b * kᴴ) = k * (1 - c • b) * kᴴ := by sorry
