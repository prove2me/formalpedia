-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_mom_add
-- name    : PositivityTheory.Rg.Sw.FFTSteps.mom_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:34.411853+00:00
-- url     : https://prove2.me/theorems/372f2f76-dde7-4bfc-9911-7c699059740f
-- title:
--   FFTSteps: mom add
-- statement:
--   The FFTSteps construction uses the mom add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L128-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L128-L135

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

theorem PositivityTheory.Rg.Sw.FFTSteps.mom_add {c : ℝ} (hc : 0 < c) (R1 R2 P : PX m n) :
    mom c ((R1 + R2) * P) = mom c (R1 * P) + mom c (R2 * P) := by sorry
