-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_norm_one_sub
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.pb_norm_one_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:49:51.641792+00:00
-- url     : https://prove2.me/theorems/2584cc0f-05a0-429d-b1b7-57b2e9092bc7
-- title:
--   GB: pb norm one sub
-- statement:
--   The GB construction uses the pb norm one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBBound.lean#L76-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBBound.lean#L76-L85

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

theorem PositivityTheory.Rg.Sw.WR.K.GB.pb_norm_one_sub (a : ℂ) (ha : a = Complex.I ∨ a = -Complex.I) (l : ℝ) :
    (1 + |l|) / Real.sqrt 2 ≤ ‖1 - a * (l : ℂ)‖ := by sorry
