-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_fderiv_detBm
-- name    : PositivityTheory.Rg.Sw.WR.B.fderiv_detBm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:00:25.642345+00:00
-- url     : https://prove2.me/theorems/f4afcfb0-18f9-466d-84de-6eeaa2f53c97
-- title:
--   B: fderiv det Bm
-- statement:
--   The B construction uses the fderiv det Bm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L71-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L71-L78

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.B.fderiv_detBm {s : ℂ} (hs : s = 1 ∨ s = -1) (y h : E n) :
    fderiv ℝ (fun y => (Bm s y).det) y h = (Bm s y).det * ((Bm s y)⁻¹ * ((Complex.I * s) • herm h)).trace := by sorry
