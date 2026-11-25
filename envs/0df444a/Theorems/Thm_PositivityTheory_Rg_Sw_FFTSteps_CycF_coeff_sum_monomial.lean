-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_coeff_sum_monomial
-- name    : PositivityTheory.Rg.Sw.FFTSteps.CycF.coeff_sum_monomial
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:00:12.680001+00:00
-- url     : https://prove2.me/theorems/8127457a-debe-5d94-8d99-a2d6060808d1
-- title:
--   Cyc F: coeff sum monomial
-- statement:
--   The Cyc F construction uses the coeff sum monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTC.lean#L67-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTC.lean#L67-L81

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.CycF
variable {m n : ℕ} (ε : Fin m → Bool)
variable {ε}

theorem PositivityTheory.Rg.Sw.FFTSteps.CycF.coeff_sum_monomial {σ R : Type*} [CommSemiring R] [DecidableEq σ] (S : Finset (σ →₀ ℕ)) (f : (σ →₀ ℕ) → R) (μ : σ →₀ ℕ) :
    coeff μ (∑ ν ∈ S, monomial ν (f ν)) = if μ ∈ S then f μ else 0 := by sorry
