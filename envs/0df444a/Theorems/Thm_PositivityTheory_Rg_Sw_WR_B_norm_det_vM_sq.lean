-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_norm_det_vM_sq
-- name    : PositivityTheory.Rg.Sw.WR.B.norm_det_vM_sq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:00:40.740358+00:00
-- url     : https://prove2.me/theorems/3329638e-2ab0-4d79-9483-1ce80ea0dfe2
-- title:
--   B: norm det v M sq
-- statement:
--   The B construction uses the norm det v M sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundA.lean#L160-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundA.lean#L160-L161

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.B.norm_det_vM_sq {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(vM s y).det‖ ^ 2 = (dP y)⁻¹ := by sorry
