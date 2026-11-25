-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_apOp_add_smul__30a907229398
-- name    : P2M_GlobalTheory_T_exists_apOp_add_smul__30a907229398
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:12.584898+00:00
-- url     : https://prove2.me/theorems/46e9f32f-38f4-44cc-9047-0f64bc8ecad0
-- title:
--   P2 M Global Theory T exists ap Op add smul  30a907229398: P2 M Global Theory T exists ap Op add smul  30a907229398
-- statement:
--   The P2 M Global Theory T exists ap Op add smul  30a907229398 construction uses the P2 M Global Theory T exists ap Op add smul  30a907229398 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsApOpAddSmulStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsApOpAddSmulStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsApOpAddSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsApOpAddSmulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_apOp_add_smul__30a907229398 : ∀ (d m m' : ℕ) (U : Set (E d)) (a a' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (t : ℂ), m' ≤ m → (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → (∀ n w, ContDiffOn ℝ ∞ (a' n w) U) → ∃ a'' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a'' n w) U) ∧ (∀ x ξ : E d, symb m a'' x ξ = symb m a x ξ + if m' = m then t * symb m' a' x ξ else 0) ∧ ∀ (u : E d → ℂ) (x : E d), apOp m a'' u x = apOp m a u x + t * apOp m' a' u x := by sorry

alias «GlobalTheory».«T».«exists_apOp_add_smul'» := P2M_GlobalTheory_T_exists_apOp_add_smul__30a907229398
