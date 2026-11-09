-- Prove2me | Theorems.Thm_StochMatchPoly_lemma_3_1
-- name    : StochMatchPoly.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:29:11.885083+00:00
-- url     : https://prove2.me/theorems/e4b91c3f-6323-402d-909a-6a79e4565291
-- title:
--   Lemma 3.1 — any randomized matching can be replaced by one with the same vertex marginals and total covariance $O(\mathbb E|M|)$
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $G(\omega)$ be a random subgraph of a finite simple graph $G=(V,E)$ with independent edge indicators, whose probabilities $q_e\in[0,1]$ need not be equal. For every randomized matching algorithm $\mathcal A$ there is another randomized matching algorithm $\mathcal A'$ such that, writing $M=\mathcal A(G(\omega))$, $M'=\mathcal A'(G(\omega))$, $X_v=\mathbf 1\{v\in V(M)\}$ and $X'_v=\mathbf 1\{v\in V(M')\}$,
--
--   1. $\mathbb E[X'_v]=\mathbb E[X_v]$ for every vertex $v$, and
--   2. $$\sum_{u,v\in V}|\operatorname{Cov}(X'_u,X'_v)|\le C\,\mathbb E|M| ,$$
--
--   the sum over ordered pairs including the diagonal.
--
--   This is the paper's key lemma: it supplies the crucial-edge matching of the main proof with vertex marginals preserved exactly and total covariance bounded independently of the maximum degree.
--
--   Differences from the source:
--   - encoding: Σ_{u,v} |Cov(X′_u, X′_v)| = O(E|M|) with absolute hidden constants (§4.1) → ∃ C > 0 fixed before the vertex type, the graph, the edge probabilities and the algorithm; reason: §4.1: constants hidden in asymptotic notation are absolute (trap 8)
--   - encoding: randomized matching algorithms A, A′ using G(ω) and private randomness → kernels π, π′ with IsRandMatching (a distribution on matchings of each realization S ⊆ E); reason: every private-randomness algorithm induces a kernel and every kernel is realized by a private seed; the paper's proof defines A′ this way
--   - encoding: a finite graph G → a finite simple graph (SimpleGraph on a Fintype); reason: §4.1: all graphs in the main argument are finite, undirected and simple
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), Lemma 3.1, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_StochMatchPoly_edgeLaw
import Definitions.Def_StochMatchPoly_IsRandMatching

open Classical

universe u

namespace StochMatchPoly

/-- S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), Lemma 3.1, p.4 (PDF p.5).

"Let G(ω) be a random subgraph of a finite graph G = (V, E), with independent edge indicators;
their probabilities need not be equal. For every randomized matching algorithm A, there is another
randomized matching algorithm A′ with the following property. Write M = A(G(ω)), M′ = A′(G(ω)),
X_v = 1{v∈V(M)}, X′_v = 1{v∈V(M′)}. Then E[X_v] = E[X′_v] for every vertex v, and
Σ_{u,v∈V} |Cov(X′_u, X′_v)| = O(E|M|). (2)"

**Formalization Note.** `O(·)` is an absolute constant (§4.1: "Constants hidden in asymptotic
notation are absolute"): `C` is chosen before the vertex type, the graph, the edge probabilities
and the algorithm. Randomized matching algorithms are kernels from realizations to distributions
on matchings of the realization (`IsRandMatching`); edge probabilities `q e ∈ [0, 1]` are
arbitrary. The covariance is under `A′`'s joint law, `E|M|` under `A`'s. The sum runs over
ordered pairs including the diagonal (§4.1). -/
theorem lemma_3_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (q : Sym2 V → ℝ),
      (∀ e ∈ G.edgeFinset, 0 ≤ q e ∧ q e ≤ 1) →
      ∀ π : Finset (Sym2 V) → Finset (Sym2 V) → ℝ, IsRandMatching G.edgeFinset π →
      ∃ π' : Finset (Sym2 V) → Finset (Sym2 V) → ℝ, IsRandMatching G.edgeFinset π' ∧
        (∀ v, marg q G.edgeFinset π' v = marg q G.edgeFinset π v) ∧
        ∑ u, ∑ v, |covCover q G.edgeFinset π' u v| ≤ C * expectedSize q G.edgeFinset π := by sorry

end StochMatchPoly
