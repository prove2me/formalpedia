-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_norm_iteratedFDeriv_cexp_phase_le__50ac9bcc8645
-- name    : P2M_GlobalTheory_T_norm_iteratedFDeriv_cexp_phase_le__50ac9bcc8645
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:51.000827+00:00
-- url     : https://prove2.me/theorems/2c4c4e7c-9815-43ae-b451-8cbf994ce74e
-- title:
--   P2 M Global Theory T norm iterated FDeriv cexp phase le  50ac9bcc8645: P2 M Global Theory T norm iterated FDeriv cexp phase le  50ac9bcc8645
-- statement:
--   The P2 M Global Theory T norm iterated FDeriv cexp phase le  50ac9bcc8645 construction uses the P2 M Global Theory T norm iterated FDeriv cexp phase le  50ac9bcc8645 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivCexpPhaseLeStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivCexpPhaseLeStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivCexpPhaseLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivCexpPhaseLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_norm_iteratedFDeriv_cexp_phase_le__50ac9bcc8645 : ∀ {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (B : V →L[ℝ] E →L[ℝ] ℂ) (h : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h → (∀ y t, (B y t + h t).re = 0) → ∀ (n : ℕ) (R : ℝ), ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (fun t => Complex.exp (B y t + h t)) t‖ ≤ C * (1 + ‖y‖) ^ n := by sorry

alias «GlobalTheory».«T».«norm_iteratedFDeriv_cexp_phase_le'» := P2M_GlobalTheory_T_norm_iteratedFDeriv_cexp_phase_le__50ac9bcc8645
