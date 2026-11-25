-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_continuous_gs
-- name    : PositivityTheory.Rg.Sw.FFTSteps.continuous_gs
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:00:31.110872+00:00
-- url     : https://prove2.me/theorems/0938ae19-98a0-5490-acc8-1c5ab0de2e75
-- title:
--   FFTSteps: continuous gs
-- statement:
--   The FFTSteps construction uses the continuous gs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L16-L18

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

theorem PositivityTheory.Rg.Sw.FFTSteps.continuous_gs (c : ℝ) : Continuous fun x : Fin m → Fin n → ℂ => gs c x := by sorry
