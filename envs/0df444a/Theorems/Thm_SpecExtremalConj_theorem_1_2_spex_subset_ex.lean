-- Prove2me | Theorems.Thm_SpecExtremalConj_theorem_1_2_spex_subset_ex
-- name    : SpecExtremalConj.theorem_1_2_spex_subset_ex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:14:06.190267+00:00
-- url     : https://prove2.me/theorems/0e13dc2a-d89e-4766-830b-1e661071e47a
-- title:
--   Theorem 1.2: $\mathrm{Ex}_{sp}(n,F)\subseteq\mathrm{Ex}(n,F)$ when $\mathrm{Ex}(n,F)$ is $T_{n,r}$ plus $O(1)$ edges
-- statement:
--   Let $r\ge2$ be an integer and let $F$ be a finite graph such that the graphs in $\mathrm{Ex}(n,F)$ are obtained from the Turán graph $T_{n,r}$ by adding $O(1)$ edges: there are constants $A$ and $n_1$ such that for every $n\ge n_1$, every $n$-vertex $F$-free graph with the maximum number $\mathrm{ex}(n,F)$ of edges contains a spanning copy of $T_{n,r}$ and has at most $e(T_{n,r})+A$ edges. Then there is $N$ such that for every $n\ge N$: if $G$ has the maximum spectral radius over all $n$-vertex $F$-free graphs, then
--
--   $$G\in\mathrm{Ex}(n,F),$$
--
--   that is, $G$ is $F$-free and $e(G)=\mathrm{ex}(n,F)$.
--
--   This confirms the conjecture of Cioabă, Desai and Tait (Conjecture 1.1): $\mathrm{Ex}_{sp}(n,F)\subseteq\mathrm{Ex}(n,F)$ for sufficiently large $n$. It contains as special cases the spectral Turán theorem for $K_{r+1}$ (Nikiforov) and the known results for friendship graphs and intersecting cliques.
--
--   Differences from the source:
--   - reading: the graphs in Ex(n, F) are obtained from T_{n,r} by adding O(1) edges → at most A added edges for a constant A, the number may vary with n (IsTuranPlusO1); reason: O(1) is a bound, not a constant number of edges; this is the weaker hypothesis and so the stronger theorem (the paper's §3 reduction to a constant a is a milestone)
--   - reading: "the graphs in Ex(n, F)" → every member of Ex(n, F), for every n ≥ n₁; reason: the hypothesis is needed only at large orders; a threshold is the weaker hypothesis
--   - encoding: "obtained from T_{n,r} by adding edges" → contains a relabelled spanning copy of turanGraph n r (ContainsSpanningTuran), with the number of added edges read off the edge count; reason: graphs are taken up to isomorphism; a graph contains a spanning T_{n,r} with k further edges exactly when it is T_{n,r} plus k edges
--   - encoding: λ(G), the largest eigenvalue of A(G) → specRad G, the supremum of the eigenvalues of the real symmetric matrix G.adjMatrix ℝ; reason: the supremum of the (finitely many, real) eigenvalues is the largest one; same value on every graph
--   - encoding: an n-vertex graph → a simple graph on Fin n; reason: the spectral radius, F-freeness and edge counts are invariant under relabelling, so every n-vertex graph is an instance
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, Theorem 1.2, p. 2

import Mathlib
import Definitions.Def_SpecExtremalConj_IsSpecExtremal
import Definitions.Def_SpecExtremalConj_IsTuranPlusO1
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **Theorem 1.2 (Ex_sp(n, F) ⊆ Ex(n, F)).** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, Theorem 1.2, p. 2: "Let r ≥ 2 be an integer,
and F be any graph such that the graphs in Ex(n, F) are obtained from T_{n,r} by adding O(1)
edges. For sufficiently large n, if G has the maximal spectral radius over all n-vertex F-free
graphs, then G ∈ Ex(n, F)." This confirms Conjecture 1.1 (Cioabă–Desai–Tait), p. 2.

Let `r ≥ 2` and let `F` be a finite graph such that, for some `A` and all large `n`, every
`n`-vertex F-free graph with the maximum number of edges is a relabelled Turán graph T_{n,r} plus
at most `A` edges. Then there is `N` such that for every `n ≥ N`, every F-free graph `G` on `Fin n`
whose largest adjacency eigenvalue is maximum among F-free graphs on `Fin n` has the maximum
number of edges among F-free graphs on `Fin n` (`G.IsExtremal F.Free`, i.e. `G ∈ Ex(n, F)`).

**Formalization Note.** O(1) is read as a bound `A` that may vary with `n` (not a constant
number `a` of added edges), the weaker hypothesis; "the graphs in Ex(n, F)" is every member of
Ex(n, F) for `n` beyond some `n₁` (`IsTuranPlusO1`). λ is the largest eigenvalue of the real
adjacency matrix (`specRad`). `N` depends on `F`, `r` and the data of the hypothesis. -/
theorem theorem_1_2_spex_subset_ex {W : Type*} [Fintype W] (F : SimpleGraph W) (r : ℕ)
    (hr : 2 ≤ r) (hF : IsTuranPlusO1 F r) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      IsSpecExtremal F G → G.IsExtremal F.Free := by sorry

end SpecExtremalConj
