-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_det_one_mul_stdBlock__3eecc0306492
-- name    : P2M_GlobalTheory_T_exists_det_one_mul_stdBlock__3eecc0306492
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:34.640191+00:00
-- url     : https://prove2.me/theorems/eefd3a53-037d-40d1-9f1d-224281c9c7eb
-- title:
--   P2 M Global Theory T exists det one mul std Block  3eecc0306492: P2 M Global Theory T exists det one mul std Block  3eecc0306492
-- statement:
--   The P2 M Global Theory T exists det one mul std Block  3eecc0306492 construction uses the P2 M Global Theory T exists det one mul std Block  3eecc0306492 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDetOneMulStdBlockStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDetOneMulStdBlockStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDetOneMulStdBlock
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDetOneMulStdBlockStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_det_one_mul_stdBlock__3eecc0306492 : ∀ {K : Type} [Field K] {n r : ℕ}, r < n → ∀ y : Matrix (Fin n) (Fin r) K, y.rank = r → ∃ g : GL (Fin n) K, Matrix.GeneralLinearGroup.det g = 1 ∧ g.val * (Matrix.of fun (a : Fin n) (b : Fin r) => if (a : ℕ) = (b : ℕ) then (1 : K) else 0) = y := by sorry

alias «GlobalTheory».«T».«exists_det_one_mul_stdBlock'» := P2M_GlobalTheory_T_exists_det_one_mul_stdBlock__3eecc0306492
