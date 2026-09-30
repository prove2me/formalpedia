-- Prove2me | Theorems.Thm_WangKangXue_SpectralTuran_theorem_1_2
-- name    : WangKangXue.SpectralTuran.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:30:10.155257+00:00
-- url     : https://prove2.me/theorems/8aa4448d-1f28-4469-88fa-c9ff8427a3b8
-- title:
--   Theorem 1.2 — if Ex(n, F) is T_{n,r} plus a fixed number of edges, then Ex_sp(n, F) ⊆ Ex(n, F)
-- statement:
--   Let $r \ge 2$ be an integer, $a \ge 0$ an integer, and $F$ a graph such that for all sufficiently large $n$ the extremal graphs for $F$ are obtained from the Turán graph $T_{n,r}$ by adding $a$ edges: $\mathrm{ex}(n,F) = e(T_{n,r}) + a$ and every graph in $\mathrm{Ex}(n,F)$ contains $T_{n,r}$. Then there is $N$ such that for every $n \ge N$: if $G$ is an $n$-vertex $F$-free graph whose spectral radius is maximal over all $n$-vertex $F$-free graphs, then
--   $$
--   e(G) = \mathrm{ex}(n,F), \qquad\text{i.e.}\qquad G \in \mathrm{Ex}(n,F).
--   $$
--
--   Here $\lambda$ is the largest adjacency eigenvalue, $e(G)$ the number of edges, $\mathrm{ex}(n,F)$ the Turán number and $\mathrm{Ex}(n,F)$ the set of $F$-free $n$-vertex graphs with $\mathrm{ex}(n,F)$ edges. The theorem confirms the conjecture of Cioabă, Desai and Tait that $\mathrm{Ex}_{sp}(n,F) \subseteq \mathrm{Ex}(n,F)$ for large $n$ whenever the extremal graphs of $F$ are Turán graphs plus $O(1)$ edges. The hypothesis is satisfiable: $F = K_{r+1}$ with $a = 0$ satisfies it by Turán's theorem, and then the theorem is Nikiforov's spectral Turán theorem.
--
--   **Formalization Note** The paper's "adding $O(1)$ edges" is read, as in Section 3 (p. 4: "We may assume that the graphs in $\mathrm{Ex}(n,F)$ are obtained from $T_{n,r}$ by adding $a$ edges"), as a single constant $a$ for all large $n$; the proof needs this. The threshold $N$ depends only on $F$, $r$ and $a$. Graphs are on the vertex type `Fin n`, and the conclusion is `#G.edgeFinset = extremalNumber n F`; together with $F$-freeness of $G$ this is membership in $\mathrm{Ex}(n,F)$.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 2, Theorem 1.2

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_WangKangXue_SpectralTuran_IsSpectralExtremal
import Definitions.Def_WangKangXue_SpectralTuran_TuranPlusEdges

namespace WangKangXue.SpectralTuran

open Classical

/-- **Theorem 1.2** (Wang–Kang–Xue, arXiv:2203.10831v1, p. 2). Let `r ≥ 2` and let `F` be a
graph whose extremal graphs on `n` vertices are, for all large `n`, the Turán graph `T_{n,r}`
plus a fixed number `a` of edges. Then for all sufficiently large `n`, every `n`-vertex
`F`-free graph of maximum spectral radius has `ex(n, F)` edges, i.e. lies in `Ex(n, F)`. -/
theorem theorem_1_2 {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      G.edgeFinset.card = SimpleGraph.extremalNumber n F := by sorry

end WangKangXue.SpectralTuran
