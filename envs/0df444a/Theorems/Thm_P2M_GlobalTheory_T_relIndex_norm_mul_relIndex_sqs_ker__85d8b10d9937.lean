-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_relIndex_norm_mul_relIndex_sqs_ker__85d8b10d9937
-- name    : P2M_GlobalTheory_T_relIndex_norm_mul_relIndex_sqs_ker__85d8b10d9937
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:21.580388+00:00
-- url     : https://prove2.me/theorems/2acfe24f-9205-4771-86ab-bec3944daca2
-- title:
--   P2 M Global Theory T rel Index norm mul rel Index sqs ker  85d8b10d9937: P2 M Global Theory T rel Index norm mul rel Index sqs ker  85d8b10d9937
-- statement:
--   The P2 M Global Theory T rel Index norm mul rel Index sqs ker  85d8b10d9937 construction uses the P2 M Global Theory T rel Index norm mul rel Index sqs ker  85d8b10d9937 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexNormMulRelIndexSqsKerStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexNormMulRelIndexSqsKerStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexNormMulRelIndexSqsKer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexNormMulRelIndexSqsKerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_relIndex_norm_mul_relIndex_sqs_ker__85d8b10d9937 : ∀ (A : Type) [CommGroup A] (σ : A →* A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → (MonoidHom.id A * σ).range.relIndex (σ.eqLocus (MonoidHom.id A)) * (sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) := by sorry

alias «GlobalTheory».«T».«relIndex_norm_mul_relIndex_sqs_ker'» := P2M_GlobalTheory_T_relIndex_norm_mul_relIndex_sqs_ker__85d8b10d9937
