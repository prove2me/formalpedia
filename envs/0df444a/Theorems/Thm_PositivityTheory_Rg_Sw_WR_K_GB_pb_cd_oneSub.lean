-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_cd_oneSub
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.pb_cd_oneSub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:40.348252+00:00
-- url     : https://prove2.me/theorems/7b728d41-ef3a-4c4a-9dad-5e99ab251e8d
-- title:
--   GB: pb cd one Sub
-- statement:
--   The GB construction uses the pb cd one Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBBound.lean#L265-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBBound.lean#L265-L268

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

theorem PositivityTheory.Rg.Sw.WR.K.GB.pb_cd_oneSub (c : ℂ) (i j : Fin n) : ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => (1 - c • b) i j) := by sorry
