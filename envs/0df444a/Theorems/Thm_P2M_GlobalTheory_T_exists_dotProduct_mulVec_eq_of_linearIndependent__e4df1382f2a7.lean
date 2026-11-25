-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_dotProduct_mulVec_eq_of_linearIndependent__e4df1382f2a7
-- name    : P2M_GlobalTheory_T_exists_dotProduct_mulVec_eq_of_linearIndependent__e4df1382f2a7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:24.8095+00:00
-- url     : https://prove2.me/theorems/3d28bb3a-c7f9-40fc-88e2-09fd86e4f36f
-- title:
--   P2 M Global Theory T exists dot Product mul Vec eq of linear Independent  e4df1382f2a7: P2 M Global Theory T exists dot Product mul Vec eq of linear Independent  e4df1382f2a7
-- statement:
--   The P2 M Global Theory T exists dot Product mul Vec eq of linear Independent  e4df1382f2a7 construction uses the P2 M Global Theory T exists dot Product mul Vec eq of linear Independent  e4df1382f2a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsDotProductMulVecEqOfLinearIndependentStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsDotProductMulVecEqOfLinearIndependentStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDotProductMulVecEqOfLinearIndependent
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDotProductMulVecEqOfLinearIndependentStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_dotProduct_mulVec_eq_of_linearIndependent__e4df1382f2a7 : ∀ (r k : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε : Fin k → Fin r → ℚ), Mq.det ≠ 0 → LinearIndependent ℚ ε → ∀ t : Fin k → ℚ, ∃ x : Fin r → ℚ, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = t i := by sorry

alias «GlobalTheory».«T».«exists_dotProduct_mulVec_eq_of_linearIndependent'» := P2M_GlobalTheory_T_exists_dotProduct_mulVec_eq_of_linearIndependent__e4df1382f2a7
