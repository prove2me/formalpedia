-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_exists_points
-- name    : PositivityTheory.Rg.Sw.FFTSteps.AsmA.exists_points
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:08:54.237488+00:00
-- url     : https://prove2.me/theorems/faff12ab-8a17-4d09-95a6-107cb1685685
-- title:
--   Asm A: exists points
-- statement:
--   The Asm A construction uses the exists points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyTB.lean#L116-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyTB.lean#L116-L140

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmA
variable {ι A B : Type} [Fintype ι] [DecidableEq ι]

theorem PositivityTheory.Rg.Sw.FFTSteps.AsmA.exists_points {σ : Type} [Fintype σ] (W : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ W]
    (ℓ : W →ₗ[ℂ] ℂ) : ∃ c : (σ → ℂ) →₀ ℂ, ∀ q : W, ℓ q = c.sum fun z a => a * eval z (q : MvPolynomial σ ℂ) := by sorry
