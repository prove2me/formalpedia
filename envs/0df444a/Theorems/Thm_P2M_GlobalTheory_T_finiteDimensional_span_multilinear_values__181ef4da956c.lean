-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_finiteDimensional_span_multilinear_values__181ef4da956c
-- name    : P2M_GlobalTheory_T_finiteDimensional_span_multilinear_values__181ef4da956c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:46.691537+00:00
-- url     : https://prove2.me/theorems/38d8cd72-8684-44f9-a586-ab172949409f
-- title:
--   P2 M Global Theory T finite Dimensional span multilinear values  181ef4da956c: P2 M Global Theory T finite Dimensional span multilinear values  181ef4da956c
-- statement:
--   The P2 M Global Theory T finite Dimensional span multilinear values  181ef4da956c construction uses the P2 M Global Theory T finite Dimensional span multilinear values  181ef4da956c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FiniteDimensionalSpanMultilinearValuesStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FiniteDimensionalSpanMultilinearValuesStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FiniteDimensionalSpanMultilinearValues
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FiniteDimensionalSpanMultilinearValuesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_finiteDimensional_span_multilinear_values__181ef4da956c : ∀ {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] (F : Type) [AddCommGroup F] [Module ℂ F] (T : MultilinearMap ℂ E F) (W : ∀ i, Submodule ℂ (E i)), (∀ i, FiniteDimensional ℂ (W i)) → FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v}) := by sorry

alias «GlobalTheory».«T».«finiteDimensional_span_multilinear_values'» := P2M_GlobalTheory_T_finiteDimensional_span_multilinear_values__181ef4da956c
