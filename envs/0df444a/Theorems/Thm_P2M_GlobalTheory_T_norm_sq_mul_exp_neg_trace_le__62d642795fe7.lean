-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_norm_sq_mul_exp_neg_trace_le__62d642795fe7
-- name    : P2M_GlobalTheory_T_norm_sq_mul_exp_neg_trace_le__62d642795fe7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:03.28236+00:00
-- url     : https://prove2.me/theorems/666dee42-3cfe-4e26-a50c-89612db44e3c
-- title:
--   P2 M Global Theory T norm sq mul exp neg trace le  62d642795fe7: P2 M Global Theory T norm sq mul exp neg trace le  62d642795fe7
-- statement:
--   The P2 M Global Theory T norm sq mul exp neg trace le  62d642795fe7 construction uses the P2 M Global Theory T norm sq mul exp neg trace le  62d642795fe7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormSqMulExpNegTraceLeStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormSqMulExpNegTraceLeStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormSqMulExpNegTraceLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormSqMulExpNegTraceLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_norm_sq_mul_exp_neg_trace_le__62d642795fe7 : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : ℝ), 0 < δ → ∃ C : ℝ, ∀ x : F, (∀ τ : Emb F, 0 < τ x) → |(Algebra.norm ℚ x : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x) ≤ C * Real.exp (-(δ / 2) * ∑ τ : Emb F, τ x) := by sorry

alias «GlobalTheory».«T».«norm_sq_mul_exp_neg_trace_le'» := P2M_GlobalTheory_T_norm_sq_mul_exp_neg_trace_le__62d642795fe7
