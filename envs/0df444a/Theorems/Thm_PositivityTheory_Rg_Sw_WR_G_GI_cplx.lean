-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_cplx
-- name    : PositivityTheory.Rg.Sw.WR.G.GI.cplx
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:05:33.94716+00:00
-- url     : https://prove2.me/theorems/c3cafdc6-1941-5ef4-9abc-27bd3e265cb5
-- title:
--   GI: cplx
-- statement:
--   The GI construction uses the cplx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/NormMono.lean#L33-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/NormMono.lean#L33-L59

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_NormMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G PositivityTheory.Rg.Sw.WR.G.GI
open PositivityTheory.Rg.Sw

theorem PositivityTheory.Rg.Sw.WR.G.GI.cplx (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Integrable fun z : ℂ => ‖z‖ ^ k * Real.exp (-c * ‖z‖ ^ 2) := by sorry
