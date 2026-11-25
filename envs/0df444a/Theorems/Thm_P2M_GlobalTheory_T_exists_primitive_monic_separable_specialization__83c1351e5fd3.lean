-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_primitive_monic_separable_specialization__83c1351e5fd3
-- name    : P2M_GlobalTheory_T_exists_primitive_monic_separable_specialization__83c1351e5fd3
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:34.879394+00:00
-- url     : https://prove2.me/theorems/4c77b780-6fc3-421d-9d40-5a869a4bd1bb
-- title:
--   P2 M Global Theory T exists primitive monic separable specialization  83c1351e5fd3: P2 M Global Theory T exists primitive monic separable specialization  83c1351e5fd3
-- statement:
--   The P2 M Global Theory T exists primitive monic separable specialization  83c1351e5fd3 construction uses the P2 M Global Theory T exists primitive monic separable specialization  83c1351e5fd3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveMonicSeparableSpecializationStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveMonicSeparableSpecializationStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveMonicSeparableSpecialization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveMonicSeparableSpecializationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_primitive_monic_separable_specialization__83c1351e5fd3 : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin D → K), IsTranscendenceBasis ℚ x → ∀ (J : Type) [Finite J] (e : J → K), ∃ (P : Polynomial (MvPolynomial (Fin D) ℚ)) (ψ : AdjoinRoot P →ₐ[ℚ] K) (g : K) (c : Fin D → ℚ), P.Monic ∧ Function.Injective ψ ∧ (∀ i, ψ (AdjoinRoot.of P (MvPolynomial.X i)) = x i) ∧ g ≠ 0 ∧ (∀ j, g * e j ∈ ψ.range) ∧ (P.map (MvPolynomial.eval c)).Separable := by sorry

alias «GlobalTheory».«T».«exists_primitive_monic_separable_specialization'» := P2M_GlobalTheory_T_exists_primitive_monic_separable_specialization__83c1351e5fd3
