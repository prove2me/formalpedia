-- Prove2me | Theorems.Thm_PredAdvice_Supplement_theorem_1_8
-- name    : PredAdvice.Supplement.theorem_1_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:32:46.546436+00:00
-- url     : https://prove2.me/theorems/b504667c-88fc-404f-be56-d78400a21a01
-- title:
--   Theorem 1.8 — exact one-missing spanners with $O(n^2(1+\log RS(n))/RS(n)^{1/3})=o(n^2)$ edges
-- statement:
--   Let $RS(n)$ be the Ruzsa–Szemerédi function and logarithms base $2$. There is an absolute constant $C$ such that for every $n\ge2$, every directed unweighted $n$-vertex graph $G$ has an exact one-missing spanner $M$ with
--
--   $$|E(M)|\le C\,\frac{n^2\,(1+\log RS(n))}{RS(n)^{1/3}},$$
--
--   and moreover
--
--   $$\frac{1+\log RS(n)}{RS(n)^{1/3}}\longrightarrow0\qquad(n\to\infty),$$
--
--   so the bound is $o(n^2)$. In the paper's notation, $\mathrm{Miss}^{\to}_1(n)=O\big(n^2(1+\log RS(n))/RS(n)^{1/3}\big)=o(n^2)$.
--
--   An exact 0-missing spanner must keep every edge, so the theorem shows that allowing one missing edge per shortest path reduces the worst-case size from $\Theta(n^2)$ to $o(n^2)$, answering Question 1.3.
--
--   **Formalization Note** The $o(n^2)$ clause is stated as the limit of the ratio, as for the base mission's goal.
--
--   Differences from the source:
--   - reading: Miss→₁(n) = O(n²f(n)) = o(n²), a max over graphs of a min over spanners → ∃ C, ∀ n ≥ 2, ∀ G : Digraph (Fin n), ∃ one-missing spanner M with edgeCount M ≤ C·n²f(n); and f(n) → 0; reason: the definition of the max/min, of O and of o, unfolded
--   - encoding: every n (“for any natural n”, or n unrestricted) → n ≥ 2; reason: RS(n) is undefined for n ≤ 1 (the published RS returns 0 there), and on at most one vertex no pair needs a hop or an edge
--   - encoding: spanning subgraph M ⊆ G and its number of edges → a Digraph M on the same vertices with M.Adj → G.Adj; size = number of ordered pairs with M.Adj (loops counted); reason: same objects; counting loops can only make the upper bound harder
--   - encoding: directed unweighted n-vertex graph → Mathlib Digraph (Fin n) (loops allowed); reason: a loop never lies on a shortest path, so distances and shortest paths are unchanged, and M may drop it
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), Theorem 1.8, p.6 (pdf p.6); Miss→_r(n), pp.4–5; proof §6, p.25

import Mathlib
import Definitions.Def_PredAdvice_RS
import Definitions.Def_PredAdvice_Supplement_IsMissingSpanner

set_option autoImplicit false

namespace PredAdvice

namespace Supplement

open Filter Topology

/-- **Theorem 1.8** (one-missing spanners; Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §1.2, p.6; proof §6, p.25).
`Miss→₁(n) = O(n² (1 + log RS(n))/RS(n)^{1/3}) = o(n²)`.

**Formalization Note**
* `Miss→₁(n)` is the maximum over directed `n`-vertex graphs of the minimum number of edges of an
  exact one-missing spanner. The `O` bound: one absolute constant `C` such that for every `n ≥ 2`
  every digraph on `Fin n` has an exact one-missing spanner with at most
  `C · n²(1 + log₂ RS(n))/RS(n)^{1/3}` edges.
* `= o(n²)` is the second conjunct: `(1 + log₂ RS(n))/RS(n)^{1/3} → 0`.
* `n ≥ 2`: `RS(n)` is undefined for `n ≤ 1`. -/
theorem theorem_1_8 :
    (∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ G : Digraph (Fin n), ∃ M : Digraph (Fin n),
      IsMissingSpanner G 1 M ∧
        (edgeCount M : ℝ) ≤ C * ((n : ℝ) ^ 2 * (1 + Real.logb 2 (RS n)) / RS n ^ (1 / 3 : ℝ))) ∧
    Tendsto (fun n : ℕ => (1 + Real.logb 2 (RS n)) / RS n ^ (1 / 3 : ℝ)) atTop (𝓝 0) := by sorry

end Supplement

end PredAdvice
