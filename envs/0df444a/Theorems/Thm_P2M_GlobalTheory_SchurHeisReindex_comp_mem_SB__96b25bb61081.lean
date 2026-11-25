-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SchurHeisReindex_comp_mem_SB__96b25bb61081
-- name    : P2M_GlobalTheory_SchurHeisReindex_comp_mem_SB__96b25bb61081
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:55.429319+00:00
-- url     : https://prove2.me/theorems/f88ab0f8-0560-47fb-a629-8ed8d2a4b8e1
-- title:
--   P2 M Global Theory Schur Heis Reindex comp mem SB  96b25bb61081: P2 M Global Theory Schur Heis Reindex comp mem SB  96b25bb61081
-- statement:
--   The P2 M Global Theory Schur Heis Reindex comp mem SB  96b25bb61081 construction uses the P2 M Global Theory Schur Heis Reindex comp mem SB  96b25bb61081 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilRepBijectionSchwartz.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilRepBijectionSchwartz.lean#L38-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilRepBijectionSchwartz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SchurHeisReindex
variable {k : Type} [Field k] [TopologicalSpace k] {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]

theorem P2M_GlobalTheory_SchurHeisReindex_comp_mem_SB__96b25bb61081 {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : Y ≃ₜ X) {f : X → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB X) : (f ∘ e) ∈ GlobalTheory.WeilM.SB Y := by sorry

alias «GlobalTheory».«SchurHeisReindex».«comp_mem_SB'» := P2M_GlobalTheory_SchurHeisReindex_comp_mem_SB__96b25bb61081
