-- Prove2me | Theorems.Thm_StochMatchPoly_Supplement_theorem_3
-- name    : StochMatchPoly.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:23:51.007229+00:00
-- url     : https://prove2.me/theorems/0d7ce063-444e-4f39-b765-0a952a922da2
-- title:
--   Theorem 3 — lower bound: some bipartite $G$ forces $\Delta(H)=\Omega(1/(p\varepsilon))$ for every $(1-\varepsilon)$-approximate sparsifier, deterministic or randomized
-- statement:
--   There are absolute constants $c>0$ and $\varepsilon_0>0$ such that the following holds for every $p\in(0,1/2]$ and every $\varepsilon\in(0,\varepsilon_0]$.
--
--   There is a finite bipartite simple graph $G$ with the following two properties, where $G_p$ is the random subgraph of $G$ keeping each edge independently with probability $p$, $\mu$ is the maximum matching size, and $\Delta(H)$ is the maximum degree of $H$.
--
--   1. **Deterministic sparsifiers.** Every subgraph $H\subseteq G$ with
--   $$\mathbb E\,\mu(H\cap G_p)\ \ge\ (1-\varepsilon)\,\mathbb E\,\mu(G_p)$$
--   has a vertex of degree at least $c/(p\varepsilon)$ in $H$, i.e. $\Delta(H)\ge c/(p\varepsilon)$.
--   2. **Randomized sparsifiers.** Let $D\in\mathbb N$ and let $\pi$ be a probability distribution on the subgraphs of $G$, drawn independently of $G_p$, every subgraph in its support having maximum degree at most $D$. If
--   $$\sum_{H\subseteq G}\pi(H)\,\mathbb E\,\mu(H\cap G_p)\ \ge\ (1-\varepsilon)\,\mathbb E\,\mu(G_p),$$
--   then $D\ge c/(p\varepsilon)$.
--
--   The constants do not depend on $p$, $\varepsilon$ or $G$; the graph $G$ depends on $p$ and $\varepsilon$ only. The theorem shows that the factor $1/p$ in the degree bound of Theorem 1 cannot be removed, even on bipartite graphs and even with randomization.
--
--   **Formalization Note** Graphs are simple graphs on `Fin n`, bipartite meaning properly 2-colourable. Expectations over $G_p$ are finite weighted sums over edge subsets of $G$ (`expect` with constant probability $p$), and the randomized sparsifier's value is the average $\sum_H \pi(H)\,\mathbb E\,\mu(H\cap G_p)$, which expresses its independence from the test realization. Only this average, not each output, is required to reach the ratio.
--
--   Differences from the source:
--   - reading: 'for every p ∈ (0, 1/2] and sufficiently small ε > 0 … ∆(H) = Ω(1/(pε))' → ∃ c > 0, ∃ ε₀ > 0 chosen before p and ε, and for all ε ∈ (0, ε₀] the bound c/(pε) ≤ ∆(H); reason: the Ω constant and the smallness threshold could be read as depending on p; the uniform reading is the stronger one and the proof gives it (ε ≤ 1/16 and D ≥ log 2/(16pε) for every p ≤ 1/2)
--   - encoding: 'the same lower bound holds for randomized sparsifiers whose outputs obey the degree bound and are independent of the test realization' → ∀ D, ∀ distribution π on the edge subsets of G supported on subsets of maximum degree ≤ D, with Σ_H π(H) E µ(H ∩ Gp) ≥ (1 − ε) E µ(Gp), c/(pε) ≤ D (same c and the same G); reason: independence of the test realization is the product form of the joint law; a distribution over the finitely many subgraphs is every randomized sparsifier's output law
--   - encoding: a bipartite graph G, subgraphs H ⊆ G, E over Gp → a SimpleGraph on Fin n with G.Colorable 2, edge sets H ⊆ G.edgeFinset, finite sums over G.edgeFinset.powerset with the product weight ∏ p^{[e∈S]}(1 − p)^{[e∉S]}; reason: Lean convention; the paper's graphs are finite, undirected and simple (§4.1) and its construction is a finite bipartite graph
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), Appendix A, Theorem 3, p.20 (PDF p.21); proof pp.20–21 (PDF pp.21–22); goal (1), p.1 (PDF p.2)

import Mathlib
import Definitions.Def_StochMatchPoly_mu
import Definitions.Def_StochMatchPoly_edgeLaw

open Classical

namespace StochMatchPoly.Supplement

open StochMatchPoly

/-- S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), Appendix A, Theorem 3, p.20 (PDF p.21), with goal (1) of p.1 (PDF p.2).

"Theorem 3. For every p ∈ (0, 1/2] and sufficiently small ε > 0, there exists a bipartite graph G
such that every subgraph H ⊆ G satisfying E µ(H ∩ Gp) ≥ (1 − ε) E µ(Gp) must have maximum degree
∆(H) = Ω(1/(pε)). The same lower bound holds for randomized sparsifiers whose outputs obey the
degree bound and are independent of the test realization."

**Formalization Note.**
1. `Ω(1/(pε))` and "sufficiently small ε" are absolute: `c > 0` and `ε₀ > 0` are chosen before
   `p` and `ε` (the proof gives `ε₀ = 1/16`, `c = log 2 / 16`, uniformly in `p ∈ (0, 1/2]`).
2. The graph `G` is a finite simple graph on `Fin n`, chosen after `p` and `ε` and before `H`
   (and before `D` and the sparsifier); bipartite is `G.Colorable 2`.
3. `∆(H) ≥ c/(pε)` is `∃ v, c / (p * ε) ≤ degIn H v`, the degree of `v` in `H`.
4. `Gp` is the product law with every edge of `G` surviving with probability `p`; expectations
   are finite sums (`expect`). The approximation hypothesis is goal (1).
5. A randomized sparsifier is a probability distribution `π` on the edge subsets of `G`, every
   subset in its support of maximum degree at most `D`; it is independent of the test realization
   `Gp`, so its value is `∑_H π(H) · E µ(H ∩ Gp)`. Only the average over `π` is required to reach
   the ratio, and the conclusion is `D ≥ c/(pε)` with the same `c`. -/
theorem theorem_3 : ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ p ε : ℝ, 0 < p → p ≤ 1 / 2 → 0 < ε → ε ≤ ε₀ →
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.Colorable 2 ∧
      (∀ H ⊆ G.edgeFinset,
        (1 - ε) * expect (fun _ => p) G.edgeFinset (fun T => (mu T : ℝ)) ≤
          expect (fun _ => p) G.edgeFinset (fun T => (mu (H ∩ T) : ℝ)) →
        ∃ v, c / (p * ε) ≤ (degIn H v : ℝ)) ∧
      (∀ (D : ℕ) (π : Finset (Sym2 (Fin n)) → ℝ),
        (∀ H ∈ G.edgeFinset.powerset, 0 ≤ π H) →
        ∑ H ∈ G.edgeFinset.powerset, π H = 1 →
        (∀ H ∈ G.edgeFinset.powerset, π H ≠ 0 → ∀ v, degIn H v ≤ D) →
        (1 - ε) * expect (fun _ => p) G.edgeFinset (fun T => (mu T : ℝ)) ≤
          ∑ H ∈ G.edgeFinset.powerset,
            π H * expect (fun _ => p) G.edgeFinset (fun T => (mu (H ∩ T) : ℝ)) →
        c / (p * ε) ≤ (D : ℝ)) := by sorry

end StochMatchPoly.Supplement
