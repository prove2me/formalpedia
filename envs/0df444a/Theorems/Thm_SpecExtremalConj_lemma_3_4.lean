-- Prove2me | Theorems.Thm_SpecExtremalConj_lemma_3_4
-- name    : SpecExtremalConj.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:12:00.005102+00:00
-- url     : https://prove2.me/theorems/af246c9b-8300-4193-9202-5d1e1a3ea74f
-- title:
--   Lemma 3.4: $|L|\le\epsilon^{1/3}n$ and $W\subseteq L$
-- statement:
--   Throughout, $r\ge2$ and $F$ is a finite graph such that, for every $n\ge n_1$, every graph of $\mathrm{Ex}(n,F)$ is a relabelled $T_{n,r}$ plus exactly $a$ edges (the standing assumption of Section 3). "$G$" denotes any $F$-free graph on $n$ vertices of maximum spectral radius ($G\in\mathrm{Ex}_{sp}(n,F)$). A partition $V(G)=V_1\cup\dots\cup V_r$ is called **maximizing** if $\sum_{i<j}e(V_i,V_j)$ is maximum over all partitions into $r$ parts. For $\epsilon,\theta>0$ let
--   $$L=\Big\{v : d(v)\le\Big(1-\frac1r-3r\epsilon^{1/3}\Big)n\Big\}\ \ (6),\qquad W=\bigcup_{i=1}^r\{v\in V_i: d_{V_i}(v)\ge2\theta n\}\ \ (5).$$
--
--   There is $\theta_0>0$ such that for all $\theta\in(0,\theta_0)$ and all $\epsilon>0$ with $2\epsilon<\theta^3$ there is $n_0$ such that for every $n\ge n_0$, every $G\in\mathrm{Ex}_{sp}(n,F)$ and every maximizing partition of $G$:
--
--   $$|L|\le\epsilon^{1/3}n\qquad\text{and}\qquad W\subseteq L.$$
--
--   In the paper, $\theta$ and $\epsilon$ are "sufficiently small constants with $\theta<\frac{1}{100r^5\ell}$ and $2\epsilon<\theta^3$", where $\ell$ is an integer with $\ell\gg\max\{a,|V(F)|\}$; the threshold $\theta_0$ collects these conditions.
--
--   Differences from the source:
--   - reading: θ, ǫ sufficiently small constants with θ < 1/(100r⁵ℓ), 2ǫ < θ³, ℓ ≫ max{a, |V(F)|} → ∃ θ₀ > 0, ∀ θ ∈ (0, θ₀), ∀ ε > 0 with 2ε < θ³, ∃ n₀, ∀ n ≥ n₀; reason: θ₀ absorbs ℓ and the smallness of θ (ℓ occurs in no conclusion); ε is constrained only by 2ε < θ³, which forces ε < θ₀³/2; this is the strongest reading
--   - reading: §3 standing assumption: the graphs in Ex(n, F) are obtained from T_{n,r} by adding a edges (n large) → IsTuranPlusConst F r a n₁: for every n ≥ n₁, every member of Ex(n, F) contains a relabelled spanning T_{n,r} and has e(T_{n,r}) + a edges; reason: the paper uses the assumption only at large orders; a threshold n₁ is the weaker hypothesis, hence the stronger statement
--   - generalization: the partition V_1 ∪ … ∪ V_r fixed in Lemma 3.3 (one maximizing partition) → every maximizing partition P : Fin n → Fin r (IsMaxCut G P); reason: the proofs use only maximality of Σ e(V_i, V_j); a maximizing partition exists because there are finitely many, so the statement specializes to the paper's
--   - encoding: "obtained from T_{n,r} by adding edges" → contains a relabelled spanning copy of turanGraph n r (ContainsSpanningTuran), with the number of added edges read off the edge count; reason: graphs are taken up to isomorphism; a graph contains a spanning T_{n,r} with k further edges exactly when it is T_{n,r} plus k edges
--   - encoding: an n-vertex graph → a simple graph on Fin n; reason: the spectral radius, F-freeness and edge counts are invariant under relabelling, so every n-vertex graph is an instance
--   - encoding: λ(G), the largest eigenvalue of A(G) → specRad G, the supremum of the eigenvalues of the real symmetric matrix G.adjMatrix ℝ; reason: the supremum of the (finitely many, real) eigenvalues is the largest one; same value on every graph
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, Lemma 3.4, p. 5, eqs. (5), (6)

import Mathlib
import Definitions.Def_SpecExtremalConj_IsSpecExtremal
import Definitions.Def_SpecExtremalConj_IsTuranPlusConst
import Definitions.Def_SpecExtremalConj_IsMaxCut
import Definitions.Def_SpecExtremalConj_lowDegSet
import Definitions.Def_SpecExtremalConj_heavySet
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **Lemma 3.4 (few low-degree vertices; W ⊆ L).** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, Lemma 3.4, p. 5: "Let θ > 0 and ǫ > 0 be
sufficiently small constants with θ < 1/(100r⁵ℓ) and 2ǫ < θ³. We denote
W := ∪_{i=1}^r {v ∈ Vi | dVi(v) ≥ 2θn}, (5) and L := {v ∈ V(G) | d(v) ≤ (1 − 1/r − 3rǫ^{1/3})n}. (6)
Then |L| ≤ ǫ^{1/3}n and W ⊆ L." Here ℓ is "an integer satisfying ℓ ≫ max{a, |V(F)|}" (p. 4).

**Standing hypotheses (§3, p. 4).** `r ≥ 2` (Theorem 1.2) and `IsTuranPlusConst F r a n₁`: for
every `n ≥ n₁`, every graph of Ex(n, F) is a relabelled T_{n,r} plus exactly `a` edges. "G" is
any spectral extremal graph (`IsSpecExtremal F G`) on `Fin n`, n large.

There is `θ₀ > 0` such that for all `θ ∈ (0, θ₀)` and all `ε > 0` with `2ε < θ³` there is `n₀`
such that for `n ≥ n₀`, every spectral extremal `G` on `Fin n` and every maximizing partition
`P` satisfy `|L| ≤ ε^{1/3} n` and `W ⊆ L`, with `L = lowDegSet G r ε` (6) and
`W = heavySet G P θ` (5).

**Formalization Note.** "θ, ǫ sufficiently small with θ < 1/(100r⁵ℓ), ℓ ≫ max{a, |V(F)|}" is the
threshold `θ₀` (which absorbs ℓ; ℓ appears in no conclusion); ǫ is constrained only by
`2ε < θ³` (which already forces `ε < θ₀³/2`), the strongest reading. "The partition" is any maximizing partition `P : Fin n → Fin r` (`IsMaxCut G P`); the paper fixes
one (Lemma 3.3), its proofs use only maximality, so quantifying over all of them is a
generalization. -/
theorem lemma_3_4 {W : Type*} [Fintype W] (F : SimpleGraph W) (r a n₁ : ℕ) (hr : 2 ≤ r)
    (hF : IsTuranPlusConst F r a n₁) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ ε : ℝ, 0 < θ → θ < θ₀ → 0 < ε → 2 * ε < θ ^ 3 →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        IsSpecExtremal F G → ∀ P : Fin n → Fin r, IsMaxCut G P →
          (#(lowDegSet G r ε) : ℝ) ≤ ε ^ ((1 : ℝ) / 3) * n ∧
            heavySet G P θ ⊆ lowDegSet G r ε := by sorry

end SpecExtremalConj
