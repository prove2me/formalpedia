-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_pow_exp_le
-- name    : PositivityTheory.Rg.Sw.FFTSteps.PosProof.pow_exp_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:54:59.14447+00:00
-- url     : https://prove2.me/theorems/b1d131ac-f7b4-4bed-b485-05823c833fc5
-- title:
--   Pos Proof: pow exp le
-- statement:
--   The Pos Proof construction uses the pow exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/IntegralHkDiag.lean#L21-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/IntegralHkDiag.lean#L21-L42

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

theorem PositivityTheory.Rg.Sw.FFTSteps.PosProof.pow_exp_le (n : ℕ) : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
    t ^ n * Real.exp (-(t ^ 2)) ≤ C * (1 + t) ^ (-(3 : ℝ)) := by sorry
