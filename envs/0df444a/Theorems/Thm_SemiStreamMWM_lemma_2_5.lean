-- Prove2me | Theorems.Thm_SemiStreamMWM_lemma_2_5
-- name    : SemiStreamMWM.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:30:10.462492+00:00
-- url     : https://prove2.me/theorems/b6d3176f-e5b6-491e-bafa-4c25316e57fa
-- title:
--   Lemma 2.5 — Algorithm 2.1 returns a $2c^2\delta\mu_w$-optimal point in $O(1/(t^2\log W))$ iterations (corrected: $G$ has an edge)
-- statement:
--   Let $G$ have integer weights in $[1,W]$, $W\ge8$ a power of two; fix $0<t\le1/(32\log W)$ with $\delta,\eta$ as in §2.1, an oracle constant $c\ge1$, and $L$ with $\mu_w(G)/4\le L\le\mu_w(G)$. Suppose $x^{(0)}\in\mathcal P_{G,\delta}$ and
--
--   $$F_t(x^{(0)})-F_t^*\le32c^2\delta\mu_w(G).$$
--
--   Then, whatever admissible answers the oracles $\mathtt{Eval}$ and $\mathtt{Step}$ give:
--
--   1. if $G$ has at least one edge, every run of Algorithm 2.1 from $x^{(0)}$ makes at most $A/(t^2\log W)$ iterations, where $A$ depends only on $c$;
--   2. every point $x$ that Algorithm 2.1 returns is feasible, $x\in\mathcal P_{G,\delta}$, and satisfies $F_t(x)-F_t^*\le2c^2\delta\mu_w(G)$.
--
--   This is the per-phase analysis of the framework: a phase starting from the gap left by the previous phase ends with a gap sixteen times smaller.
--
--   Differences from the source:
--   - correction: the iteration bound for every graph → the iteration bound for graphs with an edge (`G.edgeSet.Nonempty →`); reason: for a graph with no edge µ_w(G) = 0 forces L = 0, the exact answer Eval(x, t, x) = 0 ≥ 3δL/4 is admissible, d = −x = 0 and Algorithm 2.1 never returns, so the printed bound is false
--   - reading: Algorithm 2.1 returns … after O(1/(t² log W)) iterations → every run, for every sequence of admissible oracle answers, has at most A/(t² log W) iterations (a run of k non-returning iterations is a list of length k + 1), and every returned point satisfies the conclusion; reason: the oracles are specified only by Definitions 2.3–2.4, so the lemma must hold for every implementation (paper.md decision 9)
--   - encoding: O(1/(t² log W)) → A / (t² log W) with ∃ A after c and before the graph, weights, t, L, x⁽⁰⁾; reason: an absolute constant for a fixed oracle constant c, as the proof's 2186c²/η gives
--   - encoding: the standing assumptions stated once for the paper and for §2.1 (integer weights in [1, W], W ≥ 8 a power of two, 0 < t ≤ 1/(32 log W)) → hypotheses `Standing G w W`, `0 < t`, `t ≤ 1/(32 * logW W)`; reason: trap 19: the section's assumptions are binders; no instance changes
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), Lemma 2.5, p.11; Algorithm 2.1, p.11; Definitions 2.3–2.4, pp.10–11

import Mathlib
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_Potential
import Definitions.Def_SemiStreamMWM_Algorithms

open Classical

namespace SemiStreamMWM

/-- J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), Lemma 2.5, p.11, for
Algorithm 2.1 (p.11) with the oracles of Definitions 2.3 and 2.4 (pp.10–11).

"Starting from x^(0) ∈ P_{G,δ} with F_t(x^(0)) − F_t^∗ ≤ 32c²δµ_w(G), Algorithm 2.1 returns a feasible
x ∈ P_{G,δ} with F_t(x) − F_t^∗ ≤ 2c²δµ_w(G) after O(1/(t² log W)) iterations."

**Formalization Note.** `c ≥ 1` is the oracle constant of Definition 2.4; the `O`-constant `A`
depends on `c` only and comes before the graph, the weights, `t`, `L` and `x⁽⁰⁾`. Algorithm 2.1's
requirements (p.11) are hypotheses: `x⁽⁰⁾ ∈ P_{G,δ}`, `µ_w(G)/4 ≤ L ≤ µ_w(G)`, and §2.1's
`0 < t ≤ 1/(32 log W)`. The iteration bound holds for **every** run, whatever admissible answers the
oracles give: a run that has made `k` non-returning iterations is a list of length `k + 1`, and
`k + 1` (the iterations including the returning one) is at most `A/(t² log W)`. The output clause
holds for every run that returns. Correction: when `G` has no edge, `µ_w(G) = 0` forces `L = 0`,
the exact answer `Eval(x, t, x) = 0 ≥ 3δL/4` is admissible at every iteration, `d = −x = 0`, and
Algorithm 2.1 never returns; the iteration bound is therefore stated for graphs with an edge. -/
theorem lemma_2_5 : ∀ c : ℝ, 1 ≤ c → ∃ A : ℝ,
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) (t L : ℝ)
      (x₀ : G.edgeSet → ℝ),
      Standing G w W → 0 < t → t ≤ 1 / (32 * logW W) →
      (mwm G w : ℝ) / 4 ≤ L → L ≤ mwm G w →
      x₀ ∈ truncPolytope G (delta W t) →
      F G w W t x₀ - Fstar G w W t ≤ 32 * c ^ 2 * delta W t * mwm G w →
      (G.edgeSet.Nonempty → ∀ xs : List (G.edgeSet → ℝ), xs.head? = some x₀ →
          xs.IsChain (Alg21Step G w W c t L) → (xs.length : ℝ) ≤ A / (t ^ 2 * logW W)) ∧
      (∀ (xs : List (G.edgeSet → ℝ)) (x : G.edgeSet → ℝ), xs.head? = some x₀ →
          xs.IsChain (Alg21Step G w W c t L) → xs.getLast? = some x → Alg21Return G w W c t L x →
          x ∈ truncPolytope G (delta W t) ∧
            F G w W t x - Fstar G w W t ≤ 2 * c ^ 2 * delta W t * mwm G w) := by sorry

end SemiStreamMWM
