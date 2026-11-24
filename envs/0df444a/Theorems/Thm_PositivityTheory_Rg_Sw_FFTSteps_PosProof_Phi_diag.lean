-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_Phi_diag
-- name    : PositivityTheory.Rg.Sw.FFTSteps.PosProof.Phi_diag
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:42:04.024793+00:00
-- url     : https://prove2.me/theorems/dd199542-7b09-4c1e-a3cb-7ef6f2e778e1
-- title:
--   Pos Proof: Phi diag
-- statement:
--   The Pos Proof construction uses the Phi diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/IntegralMonSelf.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/IntegralMonSelf.lean#L59-L64

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralMonSelf
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

theorem PositivityTheory.Rg.Sw.FFTSteps.PosProof.Phi_diag (d : ι → ℝ) (z : Sg ι A B → ℂ) :
    Phi (Matrix.diagonal fun i => (d i : ℂ)) z = fun s => (kap d s : ℂ) * z s := by sorry
