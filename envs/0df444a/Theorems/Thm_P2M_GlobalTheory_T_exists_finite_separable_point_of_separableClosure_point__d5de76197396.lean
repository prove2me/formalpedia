-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_finite_separable_point_of_separableClosure_point__d5de76197396
-- name    : P2M_GlobalTheory_T_exists_finite_separable_point_of_separableClosure_point__d5de76197396
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:09:50.027792+00:00
-- url     : https://prove2.me/theorems/3cee0613-e838-45ed-a357-8d7f4975302d
-- title:
--   P2 M Global Theory T exists finite separable point of separable Closure point  d5de76197396: P2 M Global Theory T exists finite separable point of separable Closure point  d5de76197396
-- statement:
--   The P2 M Global Theory T exists finite separable point of separable Closure point  d5de76197396 construction uses the P2 M Global Theory T exists finite separable point of separable Closure point  d5de76197396 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteSeparablePointOfSeparableClosurePoinStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteSeparablePointOfSeparableClosurePoinStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteSeparablePointOfSeparableClosurePoin
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteSeparablePointOfSeparableClosurePoinStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_finite_separable_point_of_separableClosure_point__d5de76197396 : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B], Algebra.FiniteType k B → Nonempty (B →ₐ[k] SeparableClosure k) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by sorry

alias «GlobalTheory».«T».«exists_finite_separable_point_of_separableClosure_point'» := P2M_GlobalTheory_T_exists_finite_separable_point_of_separableClosure_point__d5de76197396
