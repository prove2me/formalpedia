-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_linearIndependent_adapted_to_decreasing_chain__45b67f95c1f3
-- name    : P2M_GlobalTheory_T_exists_linearIndependent_adapted_to_decreasing_chain__45b67f95c1f3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:28.715094+00:00
-- url     : https://prove2.me/theorems/999a5fe4-bfa5-47ed-9c51-ad9f78f20a4e
-- title:
--   P2 M Global Theory T exists linear Independent adapted to decreasing chain  45b67f95c1f3: P2 M Global Theory T exists linear Independent adapted to decreasing chain  45b67f95c1f3
-- statement:
--   The P2 M Global Theory T exists linear Independent adapted to decreasing chain  45b67f95c1f3 construction uses the P2 M Global Theory T exists linear Independent adapted to decreasing chain  45b67f95c1f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLinearIndependentAdaptedToDecreasingChainAStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLinearIndependentAdaptedToDecreasingChainAStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLinearIndependentAdaptedToDecreasingChainA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLinearIndependentAdaptedToDecreasingChainAStatement
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

theorem P2M_GlobalTheory_T_exists_linearIndependent_adapted_to_decreasing_chain__45b67f95c1f3 : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (S : ℕ → Set G), (∀ i, S (i + 1) ⊆ S i) → ∀ (N : ℕ) (r : ℕ → ℕ), (∀ i, ∃ e : Fin (r i) → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i) → (∀ i, r (i + 1) ≤ r i) → ∃ (e : Fin (r 0) → G) (n : Fin (r 0) → ℕ), LinearIndependent ℤ e ∧ (∀ j, e j ∈ S (n j)) ∧ ∑ i ∈ Finset.range (N + 1), r i ≤ ∑ j, (n j + 1) := by sorry

alias «GlobalTheory».«T».«exists_linearIndependent_adapted_to_decreasing_chain'» := P2M_GlobalTheory_T_exists_linearIndependent_adapted_to_decreasing_chain__45b67f95c1f3
