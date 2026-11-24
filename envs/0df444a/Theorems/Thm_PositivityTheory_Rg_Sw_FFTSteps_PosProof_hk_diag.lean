-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_hk_diag
-- name    : PositivityTheory.Rg.Sw.FFTSteps.PosProof.hk_diag
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:11:10.613791+00:00
-- url     : https://prove2.me/theorems/eba05a29-8d8b-46d3-8f8a-166e4f78100b
-- title:
--   Pos Proof: hk diag
-- statement:
--   The Pos Proof construction uses the hk diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/IntegralHkDiag.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/IntegralHkDiag.lean#L83-L87

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Module
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.PosProof

theorem PositivityTheory.Rg.Sw.FFTSteps.PosProof.hk_diag (k : ℕ) (z : ℂ) : hk k k z = (((‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2)) : ℝ) : ℂ) := by sorry
