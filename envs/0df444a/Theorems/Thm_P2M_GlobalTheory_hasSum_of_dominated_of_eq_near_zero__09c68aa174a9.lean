-- Prove2me | Theorems.Thm_P2M_GlobalTheory_hasSum_of_dominated_of_eq_near_zero__09c68aa174a9
-- name    : P2M_GlobalTheory_hasSum_of_dominated_of_eq_near_zero__09c68aa174a9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:42.833269+00:00
-- url     : https://prove2.me/theorems/302b4439-3ed7-4a6a-b758-0a842f2b84a1
-- title:
--   P2 M Global Theory has Sum of dominated of eq near zero  09c68aa174a9: P2 M Global Theory has Sum of dominated of eq near zero  09c68aa174a9
-- statement:
--   The P2 M Global Theory has Sum of dominated of eq near zero  09c68aa174a9 construction uses the P2 M Global Theory has Sum of dominated of eq near zero  09c68aa174a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumOfDominatedOfEqNearZero.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumOfDominatedOfEqNearZero.lean#L53-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumOfDominatedOfEqNearZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology
open GlobalTheory

theorem P2M_GlobalTheory_hasSum_of_dominated_of_eq_near_zero__09c68aa174a9 : ∀ {ι : Type} (b : ι → ℂ) (c : ι → ℝ) (n : ι → ℕ) (R : ℂ → ℂ) (r ε : ℝ), (∀ i, ‖b i‖ ≤ c i) →
    (∀ x : ℝ, 0 ≤ x → x < r → Summable (fun i => c i * x ^ n i)) → 0 < ε →
    DifferentiableOn ℂ R (Metric.ball 0 r) →
    (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => b i * z ^ n i) (R z)) →
    ∀ z : ℂ, ‖z‖ < r → HasSum (fun i => b i * z ^ n i) (R z) := by sorry

alias «GlobalTheory».«hasSum_of_dominated_of_eq_near_zero'» := P2M_GlobalTheory_hasSum_of_dominated_of_eq_near_zero__09c68aa174a9
