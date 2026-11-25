-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnipotentInvariant_BiInvariant_what__0c48a7516dd9
-- name    : P2M_GlobalTheory_UnipotentInvariant_BiInvariant_what__0c48a7516dd9
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:40.476413+00:00
-- url     : https://prove2.me/theorems/bc2afccd-4d5e-4f74-b75c-11eed6fbf92d
-- title:
--   P2 M Global Theory Unipotent Invariant Bi Invariant what  0c48a7516dd9: P2 M Global Theory Unipotent Invariant Bi Invariant what  0c48a7516dd9
-- statement:
--   The P2 M Global Theory Unipotent Invariant Bi Invariant what  0c48a7516dd9 construction uses the P2 M Global Theory Unipotent Invariant Bi Invariant what  0c48a7516dd9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L66-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L66-L84

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

theorem P2M_GlobalTheory_UnipotentInvariant_BiInvariant_what__0c48a7516dd9 {f : Matrix (Fin p) (Fin p) K → K} (h : BiInvariant f) (n : Fin p)
    (t : Fin p → K) (M : Matrix (Fin p) (Fin p) K) (S : Finset (Fin p)) (hS : ∀ b ∈ S, n < b) :
    f (Matrix.of fun b k => M b k + if b ∈ S then t b * M n k else 0) = f M := by sorry

alias «GlobalTheory».«UnipotentInvariant».«BiInvariant».«what₂» := P2M_GlobalTheory_UnipotentInvariant_BiInvariant_what__0c48a7516dd9
