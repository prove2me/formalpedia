-- Prove2me | Theorems.Thm_SpecExtremalConj_lemma_3_8
-- name    : SpecExtremalConj.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:13:23.822899+00:00
-- url     : https://prove2.me/theorems/3bff83fe-5e4b-495b-b4ad-8992fcf678be
-- title:
--   Lemma 3.8 (corrected: $a$ replaced by $\max(a,1)$): $x_u\ge1-20\max(a,1)^2r^2/n$
-- statement:
--   Throughout, $r\ge2$ and $F$ is a finite graph such that, for every $n\ge n_1$, every graph of $\mathrm{Ex}(n,F)$ is a relabelled $T_{n,r}$ plus exactly $a$ edges (the standing assumption of Section 3). "$G$" denotes any $F$-free graph on $n$ vertices of maximum spectral radius ($G\in\mathrm{Ex}_{sp}(n,F)$).
--
--   There is $n_0$ such that for every $n\ge n_0$, every $G\in\mathrm{Ex}_{sp}(n,F)$ and every positive eigenvector $\mathbf x$ of $A(G)$ for $\lambda(G)$ normalized by $\max_i x_i=1$,
--
--   $$x_u\ \ge\ 1-\frac{20\max(a,1)^2r^2}{n}\qquad\text{for every vertex }u.$$
--
--   All entries of the Perron vector are therefore close to the maximum entry; this drives the balancing argument of Lemma 3.10 and the final step of the proof of Theorem 1.2.
--
--   **Formalization Note** The eigenvector is a function $x:\{0,\dots,n-1\}\to\mathbb R$ with all entries positive, $A(G)x=\lambda(G)x$, all entries at most $1$ and one entry equal to $1$.
--
--   Differences from the source:
--   - correction: x_u ≥ 1 − 20a²r²/n → x_u ≥ 1 − 20·max(a, 1)²·r²/n; reason: as printed the lemma is false for a = 0: F = K₃, r = 2 satisfies the setting with a = 0 (Mantel: Ex(n, K₃) = {T_{n,2}}); for odd n the unique spectral extremal graph is T_{n,2} = K_{(n+1)/2,(n−1)/2} (Nikiforov), whose Perron vector with maximum 1 has entries √((n−1)/(n+1)) < 1 = 1 − 20·0²·r²/n; the paper's last inequality needs a ≥ 1, and with max(a, 1) the statement is unchanged for a ≥ 1 and the same proof works for a = 0
--   - reading: §3 standing assumption: the graphs in Ex(n, F) are obtained from T_{n,r} by adding a edges (n large) → IsTuranPlusConst F r a n₁: for every n ≥ n₁, every member of Ex(n, F) contains a relabelled spanning T_{n,r} and has e(T_{n,r}) + a edges; reason: the paper uses the assumption only at large orders; a threshold n₁ is the weaker hypothesis, hence the stronger statement
--   - encoding: "obtained from T_{n,r} by adding edges" → contains a relabelled spanning copy of turanGraph n r (ContainsSpanningTuran), with the number of added edges read off the edge count; reason: graphs are taken up to isomorphism; a graph contains a spanning T_{n,r} with k further edges exactly when it is T_{n,r} plus k edges
--   - encoding: an n-vertex graph → a simple graph on Fin n; reason: the spectral radius, F-freeness and edge counts are invariant under relabelling, so every n-vertex graph is an instance
--   - encoding: λ(G), the largest eigenvalue of A(G) → specRad G, the supremum of the eigenvalues of the real symmetric matrix G.adjMatrix ℝ; reason: the supremum of the (finitely many, real) eigenvalues is the largest one; same value on every graph
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, Lemma 3.8, p. 11 (normalization of x: §3, p. 4)

import Mathlib
import Definitions.Def_SpecExtremalConj_IsSpecExtremal
import Definitions.Def_SpecExtremalConj_IsTuranPlusConst
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **Lemma 3.8, corrected (all Perron entries are close to 1).** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, Lemma 3.8, p. 11:
"For any u ∈ V(G), xu ≥ 1 − 20a²r²/n", where (p. 4) "x [is] a positive eigenvector
corresponding to λ(G) with max{xi | i ∈ V(G)} = 1".

**Standing hypotheses (§3, p. 4).** `r ≥ 2` (Theorem 1.2) and `IsTuranPlusConst F r a n₁`: for
every `n ≥ n₁`, every graph of Ex(n, F) is a relabelled T_{n,r} plus exactly `a` edges. "G" is
any spectral extremal graph (`IsSpecExtremal F G`) on `Fin n`, n large.

There is `n₀` such that for `n ≥ n₀`, every spectral extremal `G` on `Fin n` and every positive
vector `x` with `A(G) x = λ(G) x` and maximum entry `1` satisfy
`x_u ≥ 1 − 20 · max(a, 1)² · r² / n` for every vertex `u`.

**Formalization Note (correction).** As printed (with `a` in place of `max(a, 1)`) the lemma is
false for `a = 0`: take `F = K₃`, `r = 2`; by Mantel's theorem Ex(n, K₃) = {T_{n,2}}, so `a = 0`;
for odd `n` the unique spectral extremal graph is T_{n,2} = K_{(n+1)/2,(n−1)/2} (Nikiforov), whose
Perron vector with maximum entry 1 has entries √((n−1)/(n+1)) < 1 = 1 − 20·0²·r²/n. The paper's
proof uses `a ≥ 1` in its last inequality; with `max(a, 1)` the statement is unchanged for
`a ≥ 1` and the same proof works for `a = 0`. -/
theorem lemma_3_8 {W : Type*} [Fintype W] (F : SimpleGraph W) (r a n₁ : ℕ) (hr : 2 ≤ r)
    (hF : IsTuranPlusConst F r a n₁) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      IsSpecExtremal F G → ∀ x : Fin n → ℝ, (∀ i, 0 < x i) →
        (G.adjMatrix ℝ).mulVec x = specRad G • x → (∀ i, x i ≤ 1) → (∃ z, x z = 1) →
          ∀ u, 1 - 20 * ((max a 1 : ℕ) : ℝ) ^ 2 * (r : ℝ) ^ 2 / n ≤ x u := by sorry

end SpecExtremalConj
