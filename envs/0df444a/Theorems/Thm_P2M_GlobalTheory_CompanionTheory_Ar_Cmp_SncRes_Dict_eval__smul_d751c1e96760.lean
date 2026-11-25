-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_eval__smul_d751c1e96760
-- name    : P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_eval__smul_d751c1e96760
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:19:57.786257+00:00
-- url     : https://prove2.me/theorems/bad1c8c0-113c-40f5-b0fe-76728a942b2d
-- title:
--   P2 M Global Theory Companion Theory Ar Cmp Snc Res Dict eval  smul d751c1e96760: P2 M Global Theory Companion Theory Ar Cmp Snc Res Dict eval  smul d751c1e96760
-- statement:
--   The P2 M Global Theory Companion Theory Ar Cmp Snc Res Dict eval  smul d751c1e96760 construction uses the P2 M Global Theory Companion Theory Ar Cmp Snc Res Dict eval  smul d751c1e96760 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AffineChartIdealPrimeAndSaturated.lean#L113-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AffineChartIdealPrimeAndSaturated.lean#L113-L127

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturated
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

theorem P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_eval__smul_d751c1e96760 {R : Type} [CommRing R] (g : ℂ →+* R) (c : K → R) (y : (Σ k, ι k) → R)
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) :
    eval₂ g (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * eval₂ g y f := by sorry

alias «GlobalTheory».«CompanionTheory».«Ar».«Cmp».«SncRes».«Dict».«eval₂_smul» := P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_eval__smul_d751c1e96760
