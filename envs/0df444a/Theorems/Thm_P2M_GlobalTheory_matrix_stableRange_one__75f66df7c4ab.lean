-- Prove2me | Theorems.Thm_P2M_GlobalTheory_matrix_stableRange_one__75f66df7c4ab
-- name    : P2M_GlobalTheory_matrix_stableRange_one__75f66df7c4ab
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:42.687631+00:00
-- url     : https://prove2.me/theorems/27171b05-dd3e-42be-823c-8439dd72502e
-- title:
--   P2 M Global Theory matrix stable Range one  75f66df7c4ab: P2 M Global Theory matrix stable Range one  75f66df7c4ab
-- statement:
--   The P2 M Global Theory matrix stable Range one  75f66df7c4ab construction uses the P2 M Global Theory matrix stable Range one  75f66df7c4ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixFieldStableRangeOneDetNeZero.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixFieldStableRangeOneDetNeZero.lean#L60-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixFieldStableRangeOneDetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem P2M_GlobalTheory_matrix_stableRange_one__75f66df7c4ab : ∀ (κ : Type) [Field κ] (n : ℕ) (c d p q : Matrix (Fin n) (Fin n) κ),
    c * p + d * q = 1 → ∃ y : Matrix (Fin n) (Fin n) κ, (c * y + d).det ≠ 0 := by sorry

alias «GlobalTheory».«matrix_stableRange_one'» := P2M_GlobalTheory_matrix_stableRange_one__75f66df7c4ab
