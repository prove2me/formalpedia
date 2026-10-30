-- Prove2me | Theorems.Thm_SpecExtremalConj_sec3_reduction_const_a
-- name    : SpecExtremalConj.sec3_reduction_const_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:10:41.267804+00:00
-- url     : https://prove2.me/theorems/e95e5a89-b9e5-4e8c-809a-2702e6d13cc7
-- title:
--   §3 (p. 4): reduction from $O(1)$ to exactly $a$ added edges
-- statement:
--   Let $r\ge2$ and let $F$ be a finite graph such that the graphs in $\mathrm{Ex}(n,F)$ are obtained from $T_{n,r}$ by adding $O(1)$ edges: there are $A$ and $n_1$ such that for every $n\ge n_1$ each $H\in\mathrm{Ex}(n,F)$ is a relabelled $T_{n,r}$ plus at most $A$ edges. Then there are constants $a$ and $n_1'$ such that
--
--   $$\text{for every } n\ge n_1',\ \text{every } H\in\mathrm{Ex}(n,F) \text{ is a relabelled } T_{n,r} \text{ plus exactly } a \text{ edges}.$$
--
--   This is the reduction with which Section 3 opens ("We may assume that the graphs in $\mathrm{Ex}(n,F)$ are obtained from $T_{n,r}$ by adding $a$ edges"); it connects the hypothesis of Theorem 1.2 to the standing assumption of all later lemmas. The paper states it without proof.
--
--   Differences from the source:
--   - reading: Turán graphs plus O(1) edges → at most A added edges for a constant A, for every n ≥ n₁ (IsTuranPlusO1); reason: O(1) is a bound, not a constant number of edges; the bounded reading is the weaker hypothesis
--   - reading: "we may assume … adding a edges" (n large) → ∃ a n₁, IsTuranPlusConst F r a n₁; reason: the paper's "n large enough" is the threshold n₁; the paper gives no argument and none is needed for the reading
--   - encoding: "obtained from T_{n,r} by adding edges" → contains a relabelled spanning copy of turanGraph n r (ContainsSpanningTuran), with the number of added edges read off the edge count; reason: graphs are taken up to isomorphism; a graph contains a spanning T_{n,r} with k further edges exactly when it is T_{n,r} plus k edges
--   - encoding: an n-vertex graph → a simple graph on Fin n; reason: the spectral radius, F-freeness and edge counts are invariant under relabelling, so every n-vertex graph is an instance
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, §3, p. 4 (unnumbered: "We may assume that the graphs in Ex(n, F) are obtained from T_{n,r} by adding a edges")

import Mathlib
import Definitions.Def_SpecExtremalConj_IsTuranPlusO1
import Definitions.Def_SpecExtremalConj_IsTuranPlusConst
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **§3 reduction to a constant number a of added edges.** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, §3, p. 4 (unnumbered): "Let F be
any graph such that the graphs in Ex(n, F) are Turán graphs plus O(1) edges. We may assume that
the graphs in Ex(n, F) are obtained from T_{n,r} by adding a edges."

If, for large `n`, every graph of Ex(n, F) is a relabelled T_{n,r} plus at most `A` edges
(`IsTuranPlusO1 F r`), then there are `a` and `n₁` such that, for every `n ≥ n₁`, every graph of
Ex(n, F) is a relabelled T_{n,r} plus exactly `a` edges (`IsTuranPlusConst F r a n₁`).

**Formalization Note.** The paper states this without argument. One argument: with
a(m) = ex(m, F) − e(T_{m,r}) ∈ [0, A], take H ∈ Ex(m+1, F) for large m; a largest Turán part of
H has more than 2A vertices, so it contains a vertex v on no added edge, and H − v is an F-free
graph on m vertices with ex(m+1, F) − (e(T_{m+1,r}) − e(T_{m,r})) edges; hence a(m+1) ≤ a(m),
and a nonincreasing sequence of naturals is eventually constant. `r ≥ 2` is the setting of
Theorem 1.2. -/
theorem sec3_reduction_const_a {W : Type*} [Fintype W] (F : SimpleGraph W) (r : ℕ) (hr : 2 ≤ r)
    (hF : IsTuranPlusO1 F r) : ∃ a n₁ : ℕ, IsTuranPlusConst F r a n₁ := by sorry

end SpecExtremalConj
