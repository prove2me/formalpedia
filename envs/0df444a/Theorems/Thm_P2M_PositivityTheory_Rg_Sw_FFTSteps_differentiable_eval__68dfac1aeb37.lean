-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_FFTSteps_differentiable_eval__68dfac1aeb37
-- name    : P2M_PositivityTheory_Rg_Sw_FFTSteps_differentiable_eval__68dfac1aeb37
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:10:48.941929+00:00
-- url     : https://prove2.me/theorems/a2696bfc-3439-5fe5-9512-5bf0a67974eb
-- title:
--   P2 M Positivity Theory Rg Sw FFTSteps differentiable eval  68dfac1aeb37: P2 M Positivity Theory Rg Sw FFTSteps differentiable eval  68dfac1aeb37
-- statement:
--   The P2 M Positivity Theory Rg Sw FFTSteps differentiable eval  68dfac1aeb37 construction uses the P2 M Positivity Theory Rg Sw FFTSteps differentiable eval  68dfac1aeb37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ExistsUnitaryDiagonalUnitary.lean#L106-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ExistsUnitaryDiagonalUnitary.lean#L106-L116

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ExistsUnitaryDiagonalUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Complex Filter Topology
open scoped ComplexConjugate ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {ι A B : Type} [Fintype ι] [DecidableEq ι]

theorem P2M_PositivityTheory_Rg_Sw_FFTSteps_differentiable_eval__68dfac1aeb37 {σ : Type} (p : MvPolynomial σ ℂ) (f : ℂ → σ → ℂ)
    (hf : ∀ v, Differentiable ℂ (fun c => f c v)) :
    Differentiable ℂ (fun c => MvPolynomial.eval (f c) p) := by sorry

alias «PositivityTheory».«Rg».«Sw».«FFTSteps».«differentiable_eval'» := P2M_PositivityTheory_Rg_Sw_FFTSteps_differentiable_eval__68dfac1aeb37
