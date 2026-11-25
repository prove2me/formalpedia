-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_fderiv_detAm
-- name    : PositivityTheory.Rg.Sw.WR.B.fderiv_detAm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:05:52.746864+00:00
-- url     : https://prove2.me/theorems/81ce0c06-8c7d-5238-9ee6-48e8a241e03b
-- title:
--   B: fderiv det Am
-- statement:
--   The B construction uses the fderiv det Am property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L62-L69

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

theorem PositivityTheory.Rg.Sw.WR.B.fderiv_detAm {s : ℂ} (hs : s = 1 ∨ s = -1) (y h : E n) :
    fderiv ℝ (fun y => (Am s y).det) y h = (Am s y).det * ((Am s y)⁻¹ * (-((Complex.I * s) • herm h))).trace := by sorry
