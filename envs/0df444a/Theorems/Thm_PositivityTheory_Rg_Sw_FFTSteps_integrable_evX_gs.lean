-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_integrable_evX_gs
-- name    : PositivityTheory.Rg.Sw.FFTSteps.integrable_evX_gs
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:18.882285+00:00
-- url     : https://prove2.me/theorems/75f6ace7-e745-5735-833a-07b66116bf5c
-- title:
--   FFTSteps: integrable ev X gs
-- statement:
--   The FFTSteps construction uses the integrable ev X gs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L88-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L88-L126

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

theorem PositivityTheory.Rg.Sw.FFTSteps.integrable_evX_gs (P : PX m n) : ∀ {c : ℝ}, 0 < c → Integrable (fun x => evX P x * gs c x) := by sorry
