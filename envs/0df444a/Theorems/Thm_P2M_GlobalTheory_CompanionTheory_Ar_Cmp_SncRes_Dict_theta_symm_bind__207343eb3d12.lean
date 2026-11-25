-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_theta_symm_bind__207343eb3d12
-- name    : P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_theta_symm_bind__207343eb3d12
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:21:27.82891+00:00
-- url     : https://prove2.me/theorems/07829af4-449f-45f0-8b00-42a749b30d8b
-- title:
--   P2 M Global Theory Companion Theory Ar Cmp Snc Res Dict theta symm bind  207343eb3d12: P2 M Global Theory Companion Theory Ar Cmp Snc Res Dict theta symm bind  207343eb3d12
-- statement:
--   The P2 M Global Theory Companion Theory Ar Cmp Snc Res Dict theta symm bind  207343eb3d12 construction uses the P2 M Global Theory Companion Theory Ar Cmp Snc Res Dict theta symm bind  207343eb3d12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AffineChartIdealPrimeAndSaturated.lean#L220-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AffineChartIdealPrimeAndSaturated.lean#L220-L248

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturated
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_theta_symm_bind__207343eb3d12 (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime]
    (p : (k : K) → ι k) (hp : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q)
    (f : MvPolynomial (Σ k, ι k) ℂ) :
    theta Q p ((renR (Σ k, ι k)).symm (bind₁ (SncRes.lift p) f)) = theta Q p f := by sorry

alias «GlobalTheory».«CompanionTheory».«Ar».«Cmp».«SncRes».«Dict».«theta_symm_bind₁» := P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_theta_symm_bind__207343eb3d12
