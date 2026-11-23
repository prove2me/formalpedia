-- Prove2me | Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_select
-- name    : UpperTheory.BernoulliSumsFrobeniusOrbits.select
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:48.966568+00:00
-- url     : https://prove2.me/theorems/0a79d4f8-e15f-4030-8093-2afc7413bc59
-- title:
--   Bernoulli Sums Frobenius Orbits: select
-- statement:
--   The Bernoulli Sums Frobenius Orbits construction uses the select property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/select.lean#L70-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/select.lean#L70-L174

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_select
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.select :
    ∀ (α κ ι : Type) [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] (cl : α → κ) (p : α → ℝ) (δ β D : ℝ)
        (I : Finset ι) (ω : ι → ℝ) (BAD : ι → α → Finset α → Prop),
      (∀ a, 0 ≤ p a ∧ p a ≤ δ) → 0 ≤ δ → δ ≤ 1 → 0 ≤ β → (∀ i, 0 ≤ ω i) → 0 < D → 2 * δ * Fintype.card α ≤ D ^ 2 →
      (∀ i ∈ I, ∀ t, ∑ T : Finset α, pw p T * ind (t ∈ T ∧ BAD i t T) ≤ β * δ) →
      ∃ T : Finset α, (∀ c : κ, |((T.filter fun a => cl a = c).card : ℝ) - ∑ a ∈ univ.filter (fun a => cl a = c), p a| ≤ D) ∧
        ∑ i ∈ I, ω i * (({t | t ∈ T ∧ BAD i t T}.ncard : ℕ) : ℝ) ≤ 4 * β * δ * Fintype.card α * ∑ i ∈ I, ω i := by sorry
