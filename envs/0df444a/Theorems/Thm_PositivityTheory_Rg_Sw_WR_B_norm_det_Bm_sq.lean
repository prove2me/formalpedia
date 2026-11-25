-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_norm_det_Bm_sq
-- name    : PositivityTheory.Rg.Sw.WR.B.norm_det_Bm_sq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:00:39.480633+00:00
-- url     : https://prove2.me/theorems/958b9466-0022-4c26-acf4-3a4ce0fba62e
-- title:
--   B: norm det Bm sq
-- statement:
--   The B construction uses the norm det Bm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundA.lean#L150-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundA.lean#L150-L155

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

theorem PositivityTheory.Rg.Sw.WR.B.norm_det_Bm_sq {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(Bm s y).det‖ ^ 2 = dP y := by sorry
