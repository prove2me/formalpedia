-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_integrable_gs_prod
-- name    : PositivityTheory.Rg.Sw.FFTSteps.integrable_gs_prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:49:59.386846+00:00
-- url     : https://prove2.me/theorems/ab2036fd-53c8-4e8e-861b-fce17ec1dec4
-- title:
--   FFTSteps: integrable gs prod
-- statement:
--   The FFTSteps construction uses the integrable gs prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L46-L50

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
set_option maxHeartbeats 1000000

theorem PositivityTheory.Rg.Sw.FFTSteps.integrable_gs_prod {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin m → Fin n → ℂ => ∏ a, ∏ i, Real.exp (-(c * ‖x a i‖ ^ 2))) := by sorry
