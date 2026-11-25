-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_phi_eq_eval__9a32e9bc08e4
-- name    : P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_phi_eq_eval__9a32e9bc08e4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:21:10.759352+00:00
-- url     : https://prove2.me/theorems/d82c2fab-9c46-4baf-af99-a8e3a139a0cb
-- title:
--   P2 M Global Theory Companion Theory Ar Cmp Snc Res Dict phi eq eval  9a32e9bc08e4: P2 M Global Theory Companion Theory Ar Cmp Snc Res Dict phi eq eval  9a32e9bc08e4
-- statement:
--   The P2 M Global Theory Companion Theory Ar Cmp Snc Res Dict phi eq eval  9a32e9bc08e4 construction uses the P2 M Global Theory Companion Theory Ar Cmp Snc Res Dict phi eq eval  9a32e9bc08e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AffineChartIdealPrimeAndSaturated.lean#L138-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AffineChartIdealPrimeAndSaturated.lean#L138-L145

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

theorem P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_phi_eq_eval__9a32e9bc08e4 (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime]
    (f : MvPolynomial (Σ k, ι k) ℂ) :
    phi Q f = eval₂ ((phi Q).comp C) (fun q => phi Q (X q)) f := by sorry

alias «GlobalTheory».«CompanionTheory».«Ar».«Cmp».«SncRes».«Dict».«phi_eq_eval₂» := P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_phi_eq_eval__9a32e9bc08e4
