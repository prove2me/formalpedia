-- Prove2me | Theorems.Thm_PredAdvice_Supplement_theorem_1_2
-- name    : PredAdvice.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:30:23.892202+00:00
-- url     : https://prove2.me/theorems/553df962-2c3d-4805-b2e8-123534830cb8
-- title:
--   Theorem 1.2 — edge-centered three-hopsets of size $O(n^2(1+\log RS(n))/RS(n)^{1/3})$
-- statement:
--   Let $RS(n)$ be the Ruzsa–Szemerédi function: $n^2/RS(n)$ is the maximum number of edges of an $n$-vertex graph whose edges split into at most $n$ induced matchings. Logarithms are base $2$.
--
--   There is an absolute constant $C$ such that for every $n\ge2$, every unweighted $n$-vertex graph $G$ — directed or undirected — has an edge-centered three-hopset $H$ with
--
--   $$|H|\le C\,\frac{n^2\,(1+\log RS(n))}{RS(n)^{1/3}} .$$
--
--   In the paper's notation, $\mathrm{Hop}_{ec3}(n)=O\big(n^2(1+\log RS(n))/RS(n)^{1/3}\big)$, where $\mathrm{Hop}_{ec3}(n)$ is the maximum over $n$-vertex graphs of the minimum size of an edge-centered three-hopset. It improves the exponent $1/6$ obtainable from Kosowski, Uznański and Viennot to $1/3$, and extends the bound to directed graphs.
--
--   **Formalization Note** The maximum and minimum are unfolded: one constant chosen before $n$ and the graph, and for each graph a hopset meeting the bound. Footnote 4 says the bound applies to directed and undirected graphs, so both clauses are stated.
--
--   Differences from the source:
--   - reading: Hop_{ec3}(n) = O(f(n)), a max over graphs of a min over hopsets → ∃ C, ∀ n ≥ 2, ∀ graph on Fin n, ∃ edge-centered three-hopset H with size ≤ C·f(n); reason: the definition of the max/min and of O, unfolded
--   - encoding: every n (“for any natural n”, or n unrestricted) → n ≥ 2; reason: RS(n) is undefined for n ≤ 1 (the published RS returns 0 there), and on at most one vertex no pair needs a hop or an edge
--   - encoding: unweighted directed / undirected n-vertex graphs → Mathlib Digraph (Fin n) (loops allowed) / SimpleGraph (Fin n); undirected distances are those of the symmetric digraph, undirected hops are unordered pairs (Sym2); reason: a loop never lies on a shortest path, so distances and hopsets are unchanged; footnote 4 reads an undirected edge as two opposite directed edges
--   - encoding: hopset size |H|, diagonal edges free (p.10) → number of off-diagonal pairs of a finite hop set; a hop between an unreachable pair is allowed but has weight ⊤ and can lie on no exact route; reason: the paper's convention; an unreachable hop only adds to the size
--   - reading: edge-centered property, “u → x → y → v … has total weight dist_G(u, v)” (p.5) → explicit clause dist(u,x) + 1_{x≠y} + dist(y,v) = dist(u,v) with (x,y) an edge of G or x = y; reason: an edge between distinct vertices has weight 1 = dist(x,y), so the clause is the page's total-weight condition written out
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), Theorem 1.2, p.5 (pdf p.5); proof §3.4, p.14; footnote 4, p.4

import Mathlib
import Definitions.Def_PredAdvice_RS
import Definitions.Def_PredAdvice_Supplement_IsExactHopset

set_option autoImplicit false

namespace PredAdvice

namespace Supplement

/-- **Theorem 1.2** (edge-centered three-hopsets upper bound; Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §1.2, p.5; proof §3.4,
p.14). For any natural `n`,
`Hop^ec_3(n) = O(n²(1 + log RS(n))/RS(n)^{1/3})`.

**Formalization Note**
* `Hop^ec_3(n)` is the maximum over `n`-vertex graphs of the minimum size of an edge-centered
  three-hopset; the bound is stated as: one absolute constant `C`, chosen before `n` and the
  graph, such that every graph on `Fin n` has an edge-centered three-hopset of size at most
  `C · n²(1 + log₂ RS(n))/RS(n)^{1/3}`.
* Footnote 4 (p.4): the bound applies to directed and to undirected graphs; both are stated.
* `n ≥ 2`: `RS(n)` is undefined for `n ≤ 1` (where no pair needs a hop). -/
theorem theorem_1_2 :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      (∀ G : Digraph (Fin n), ∃ H : Finset (Fin n × Fin n), IsEdgeCentered3Hopset G H ∧
        (hopsetSize H : ℝ) ≤
          C * ((n : ℝ) ^ 2 * (1 + Real.logb 2 (RS n)) / RS n ^ (1 / 3 : ℝ))) ∧
      (∀ G : SimpleGraph (Fin n), ∃ H : Finset (Sym2 (Fin n)), IsEdgeCentered3HopsetU G H ∧
        (hopsetSizeU H : ℝ) ≤
          C * ((n : ℝ) ^ 2 * (1 + Real.logb 2 (RS n)) / RS n ^ (1 / 3 : ℝ))) := by sorry

end Supplement

end PredAdvice
