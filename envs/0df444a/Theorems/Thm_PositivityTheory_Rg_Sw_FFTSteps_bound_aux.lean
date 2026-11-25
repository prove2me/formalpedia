-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_bound_aux
-- name    : PositivityTheory.Rg.Sw.FFTSteps.bound_aux
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:37.767373+00:00
-- url     : https://prove2.me/theorems/e3671b5f-81c7-5f50-a4e1-ec78a05a2c37
-- title:
--   FFTSteps: bound aux
-- statement:
--   The FFTSteps construction uses the bound aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L59-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L59-L77

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

theorem PositivityTheory.Rg.Sw.FFTSteps.bound_aux {a r S : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hS : r ^ 2 ≤ S) :
    r * Real.exp (-(a * S)) ≤ 1 + 1 / a := by sorry
