-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnipotentInvariant_eval_bind___d799cbbaf6da
-- name    : P2M_GlobalTheory_UnipotentInvariant_eval_bind___d799cbbaf6da
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:35.839709+00:00
-- url     : https://prove2.me/theorems/4027fb4f-97f5-4218-ade4-acd478bdb458
-- title:
--   P2 M Global Theory Unipotent Invariant eval bind   d799cbbaf6da: P2 M Global Theory Unipotent Invariant eval bind   d799cbbaf6da
-- statement:
--   The P2 M Global Theory Unipotent Invariant eval bind   d799cbbaf6da construction uses the P2 M Global Theory Unipotent Invariant eval bind   d799cbbaf6da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L239-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L239-L244

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}
variable {σ : Type*} [DecidableEq σ]
omit [DecidableEq σ]

theorem P2M_GlobalTheory_UnipotentInvariant_eval_bind___d799cbbaf6da (y : σ → K) (g : σ → MvPolynomial σ K) (P : MvPolynomial σ K) :
    eval y (bind₁ g P) = eval (fun s => eval y (g s)) P := by sorry

alias «GlobalTheory».«UnipotentInvariant».«eval_bind₁'» := P2M_GlobalTheory_UnipotentInvariant_eval_bind___d799cbbaf6da
