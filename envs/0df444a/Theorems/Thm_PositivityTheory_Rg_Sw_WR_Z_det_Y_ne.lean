-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_det_Y_ne
-- name    : PositivityTheory.Rg.Sw.WR.Z.det_Y_ne
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:09:15.735796+00:00
-- url     : https://prove2.me/theorems/1063e541-2726-502a-aa9e-3486cee6d36a
-- title:
--   Z: det Y ne
-- statement:
--   The Z construction uses the det Y ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L67-L69

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.Z.det_Y_ne (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) : (1 + (Complex.I * s) • herm y).det ≠ 0 := by sorry
