-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_norm_Phi
-- name    : PositivityTheory.Rg.Sw.FFTSteps.PosProof.norm_Phi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:27:53.338429+00:00
-- url     : https://prove2.me/theorems/71135b20-38fd-4c6f-9b88-5ae251b54765
-- title:
--   Pos Proof: norm Phi
-- statement:
--   The Pos Proof construction uses the norm Phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ContinuousPhi.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ContinuousPhi.lean#L56-L62

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.PosProof
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]

theorem PositivityTheory.Rg.Sw.FFTSteps.PosProof.norm_Phi (U : Matrix ι ι ℂ) (hU : star U * U = 1) (z : Sg ι A B → ℂ) :
    ∑ s, ‖Phi U z s‖ ^ 2 = ∑ s, ‖z s‖ ^ 2 := by sorry
