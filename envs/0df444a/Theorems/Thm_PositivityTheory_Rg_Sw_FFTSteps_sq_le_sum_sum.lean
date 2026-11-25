-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_sq_le_sum_sum
-- name    : PositivityTheory.Rg.Sw.FFTSteps.sq_le_sum_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:48:43.017643+00:00
-- url     : https://prove2.me/theorems/22b1a54d-823d-49b0-89c8-19fef303ade3
-- title:
--   FFTSteps: sq le sum sum
-- statement:
--   The FFTSteps construction uses the sq le sum sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L79-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L79-L86

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

theorem PositivityTheory.Rg.Sw.FFTSteps.sq_le_sum_sum (x : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) :
    ‖x a i‖ ^ 2 ≤ ∑ a, ∑ i, ‖x a i‖ ^ 2 := by sorry
