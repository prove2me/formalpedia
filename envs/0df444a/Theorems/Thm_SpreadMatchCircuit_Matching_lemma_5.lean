-- Prove2me | Theorems.Thm_SpreadMatchCircuit_Matching_lemma_5
-- name    : SpreadMatchCircuit.Matching.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:18.317733+00:00
-- url     : https://prove2.me/theorems/7a0c9edc-5e41-440f-b6c0-a5e055a6996a
-- title:
--   Lemma 5 (Spread Matching Lemma)
-- statement:
--   There is a universal constant $\alpha>0$ such that the following holds. Let $0<\varepsilon<1/2$, $t>1$, $0<\gamma\le 1$ with $\gamma n$ an integer, and
--
--   $$r=\alpha\cdot\frac{t+\log^2(1/\varepsilon)}{\gamma^2}.$$
--
--   Let $Z$ be an $r$-spread random matching on the vertex set $[n]$ with $|Z|\le t$, with arbitrary law and support $\mathcal Z$. If $W\subseteq[n]$ is a uniformly random set with $|W|=\gamma n$, then
--
--   $$p\big(\exists z\in\mathcal Z,\ z\subseteq G(W)\big)>1-\varepsilon.$$
--
--   The lemma says that the graph of edges incident to a random vertex set contains a matching from any sufficiently spread family, with the additive dependence $t+\log^2(1/\varepsilon)$ on the parameters. It is applied twice in the proof of Theorem 1: to the output approximator and to the conditioned residual in Lemma 12.
--
--   **Formalization Note** The probability is over $W$ only, and $\alpha$ is quantified before every other parameter. The logarithm is natural; another base would only change $\alpha$.
--
--   Differences from the source:
--   - encoding: ε < 1/2 and |W| = γn with γ's range implicit → 0 < ε < 1/2, 0 < γ ≤ 1, and a natural number w with w = γn; reason: the conclusion cannot hold for ε ≤ 0, and a set of size γn requires γ ≤ 1 with γn an integer.
--   - reading: log of unspecified base → the natural log; reason: changing the base only rescales the universal constant α.
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 4, Lemma 5 (proof pp. 6–10)

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs
import Definitions.Def_SpreadMatchCircuit_Matching_SpreadLaw

namespace SpreadMatchCircuit.Matching

/-- Lemma 5 (Spread Matching Lemma), p. 4. The constant `α` precedes all other parameters. -/
theorem lemma_5 :
    ∃ α : ℝ, 0 < α ∧
      ∀ (n : ℕ) (μ : PMF (Finset (Edge n))) (ε t γ r : ℝ) (w : ℕ),
        0 < ε → ε < 1 / 2 → 1 < t → 0 < γ → γ ≤ 1 → (w : ℝ) = γ * (n : ℝ) →
        r = α * (t + Real.log (1 / ε) ^ 2) / γ ^ 2 →
        IsBoundedMatchingLaw μ t → IsSpread μ r →
        1 - ε < uniformProb (Finset.powersetCard w (Finset.univ : Finset (Fin n)))
          (fun W => ∃ z ∈ lawSupport μ, z ⊆ incident W) := by sorry

end SpreadMatchCircuit.Matching
