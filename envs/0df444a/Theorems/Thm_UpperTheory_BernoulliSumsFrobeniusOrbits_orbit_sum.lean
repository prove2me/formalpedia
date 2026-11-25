-- Prove2me | Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_orbit_sum
-- name    : UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:04.163878+00:00
-- url     : https://prove2.me/theorems/3d47b274-c749-5bff-bab1-e447aa9359ab
-- title:
--   Bernoulli Sums Frobenius Orbits: orbit sum
-- statement:
--   The Bernoulli Sums Frobenius Orbits construction uses the orbit sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/orbitSum.lean#L134-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/orbitSum.lean#L134-L159

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_orbitSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_sum :
    ∀ (α : Type) [Fintype α] [DecidableEq α] [AddCommGroup α] (p : α → ℝ) (b h t : α), (∃ i : ℕ, b + i • h = t) →
      ∀ A : Finset ℕ → Prop, ∃ i₀ < addOrderOf h, b + i₀ • h = t ∧
        ∑ T : Finset α, pw p T * ind (t ∈ T ∧ A ((univ.filter (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T)).map Fin.valEmbedding)) =
          p t * exP (fun i => p (b + i • h)) ((range (addOrderOf h)).erase i₀) (fun U => ind (A (insert i₀ U))) := by sorry
