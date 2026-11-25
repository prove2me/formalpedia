-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_integrable_gauss1
-- name    : PositivityTheory.Rg.Sw.FFTSteps.integrable_gauss1
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:24.973609+00:00
-- url     : https://prove2.me/theorems/66b77c23-acb8-5074-8c7a-043e23f0b87e
-- title:
--   FFTSteps: integrable gauss1
-- statement:
--   The FFTSteps construction uses the integrable gauss1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L30-L35

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

theorem PositivityTheory.Rg.Sw.FFTSteps.integrable_gauss1 {c : ℝ} (hc : 0 < c) : Integrable (fun z : ℂ => Real.exp (-(c * ‖z‖ ^ 2))) := by sorry
