-- Prove2me | Theorems.Thm_SpreadMatchCircuit_Matching_Supplement_lemma_4
-- name    : SpreadMatchCircuit.Matching.Supplement.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:33:49.953865+00:00
-- url     : https://prove2.me/theorems/7e1f45e4-bde5-4db6-9d97-5cc87148296e
-- title:
--   Lemma 4 — Spread Clique Lemma
-- statement:
--   There is a universal constant $\alpha>0$ such that the following holds. Let $n$ be a natural number, $0<\varepsilon\le 1/2$, $t>0$ and $0<p\le 1$. Let $S\subseteq[n]$ be an arbitrary set of vertices and $s=|S|$. Put
--   $$r=\frac{\alpha\log(t/\varepsilon)}{p^{\,t+s}}.$$
--   Let $Z\subseteq[n]$ be a random $r$-spread set of size at most $t$ with support $\mathcal Z$; its law is arbitrary. Let $X_0$ be the random graph on $[n]$ that includes each edge independently with probability $p$, and let $C_T$ denote the clique on a vertex set $T$. Then
--   $$\Pr_{X_0}\bigl[\exists z\in\mathcal Z:\ C_{z\cup S}\subseteq X_0\cup C_S\bigr]>1-\varepsilon .$$
--
--   The lemma says that a spread family of vertex sets is hit by the random graph with high probability, even when every set must be completed to a clique together with the fixed set $S$, whose own clique is granted for free. It is used in the proof of the clique lower bound, Theorem 8.
--
--   **Formalization Note** $\log$ is the natural logarithm; a different base changes only $\alpha$. The constant $\alpha$ is chosen before $n,\mu,\varepsilon,t,p,S$. The probability is over $X_0$ only; $\mathcal Z$ is the support of the law of $Z$. The power $p^{t+s}$ is a real power.
--
--   Differences from the source:
--   - encoding: ε ≤ 1/2 → 0 < ε ≤ 1/2; reason: log(t/ε) is defined only for ε > 0
--   - encoding: size bound t → real t > 0; reason: log(t/ε) is defined only for t > 0, and a random set of size at most t ≤ 0 is empty
--   - encoding: edge probability p → 0 < p ≤ 1; reason: p is a probability and r divides by p^{t+s}
--   - encoding: a random r-spread set Z ⊆ [n] of size at most t with support 𝒵 → a PMF μ on subsets of Fin n with IsSetSpread μ r, every support member of cardinality at most t, and lawSupport μ for 𝒵; reason: same objects, arbitrary weights
--   - reading: log unspecified → natural logarithm; reason: the source fixes no base, and a change of base is absorbed into the universal constant α
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 4, Lemma 4 (Spread Clique Lemma); definition of r-spread random sets p. 3; proof pp. 13–14

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs
import Definitions.Def_SpreadMatchCircuit_Matching_SpreadLaw
import Definitions.Def_SpreadMatchCircuit_Matching_Supplement_Cliques
import Definitions.Def_SpreadMatchCircuit_Matching_Supplement_SetSpread

namespace SpreadMatchCircuit.Matching.Supplement

/-- Lemma 4 (Spread Clique Lemma), p. 4. The constant `α` precedes all other parameters; `s = |S|`
and `log` is the natural logarithm. -/
theorem lemma_4 :
    ∃ α : ℝ, 0 < α ∧
      ∀ (n : ℕ) (μ : PMF (Finset (Fin n))) (ε t p r : ℝ) (S : Finset (Fin n)),
        0 < ε → ε ≤ 1 / 2 → 0 < t → 0 < p → p ≤ 1 →
        r = α * Real.log (t / ε) / p ^ (t + (S.card : ℝ)) →
        IsSetSpread μ r → IsBoundedSetLaw μ t →
        1 - ε < randomGraphProb n p
          (fun X => ∃ z ∈ lawSupport μ, cliqueEdges (z ∪ S) ⊆ X ∪ cliqueEdges S) := by sorry

end SpreadMatchCircuit.Matching.Supplement
