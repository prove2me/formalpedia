-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_integrable_gs_row
-- name    : PositivityTheory.Rg.Sw.FFTSteps.integrable_gs_row
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:51:39.584143+00:00
-- url     : https://prove2.me/theorems/ffb013a2-8c95-5089-bc0a-26254aae2147
-- title:
--   FFTSteps: integrable gs row
-- statement:
--   The FFTSteps construction uses the integrable gs row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L41-L43

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_NullTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.FFTSteps.integrable_gs_row {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : Fin n → ℂ => ∏ i, Real.exp (-(c * ‖y i‖ ^ 2))) := by sorry
