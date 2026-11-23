-- Prove2me | Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_expectation_spec
-- name    : UpperTheory.BernoulliSumsFrobeniusOrbits.expectation_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:58.060579+00:00
-- url     : https://prove2.me/theorems/684309ef-9fd7-46fe-98a5-ae811bcfc3f3
-- title:
--   Bernoulli Sums Frobenius Orbits: expectation spec
-- statement:
--   The Bernoulli Sums Frobenius Orbits construction uses the expectation spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/expectationSpec.lean#L133-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/expectationSpec.lean#L133-L148

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_expectationSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.expectation_spec :
    ∀ (p : ℕ → ℝ),
      (∀ (S : Finset ℕ) (c : ℝ), exP p S (fun _ => c) = c) ∧
      (∀ (S : Finset ℕ) (f g : Finset ℕ → ℝ), exP p S (fun T => f T + g T) = exP p S f + exP p S g) ∧
      (∀ (S : Finset ℕ) (I : Finset ℕ) (f : ℕ → Finset ℕ → ℝ), exP p S (fun T => ∑ i ∈ I, f i T) = ∑ i ∈ I, exP p S (f i)) ∧
      (∀ (S : Finset ℕ) (f g : Finset ℕ → ℝ), (∀ a ∈ S, 0 ≤ p a ∧ p a ≤ 1) → (∀ T ⊆ S, f T ≤ g T) → exP p S f ≤ exP p S g) ∧
      (∀ (a : ℕ) (S : Finset ℕ) (f : Finset ℕ → ℝ), a ∉ S →
        exP p (insert a S) f = (1 - p a) * exP p S f + p a * exP p S (fun T => f (insert a T))) ∧
      (∀ (A S : Finset ℕ) (f : Finset ℕ → ℝ), A ⊆ S → exP p S (fun T => f (T ∩ A)) = exP p A f) ∧
      (∀ (J : Finset ℕ) (A : ℕ → Finset ℕ) (g : ℕ → Finset ℕ → ℝ) (S : Finset ℕ),
        (∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (A i) (A j)) → (∀ j ∈ J, A j ⊆ S) →
        exP p S (fun T => ∏ j ∈ J, g j (T ∩ A j)) = ∏ j ∈ J, exP p (A j) (g j)) := by sorry
