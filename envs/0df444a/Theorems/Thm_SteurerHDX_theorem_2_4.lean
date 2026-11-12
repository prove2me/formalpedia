-- Prove2me | Theorems.Thm_SteurerHDX_theorem_2_4
-- name    : SteurerHDX.theorem_2_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:35:40.289068+00:00
-- url     : https://prove2.me/theorems/614ac4c1-dbdd-49b9-b290-2b23064a1993
-- title:
--   Theorem 2.4: sparse pure $d$-partite $1/(2d)$-top-link expanders with $\lambda_2(P_d^\vee)\le 1-1/(ed)$
-- statement:
--   This is the existence of sparse high-dimensional expanders used by the paper.
--
--   There are absolute constants $c_1,c_2,C>0$ such that for all integers $1\le k<r$, with $d=2k+1$, and every prime power $q\ge(4d+1)^2$, there is a simplicial complex $\mathcal X$ with:
--
--   1. $\mathcal X$ pure $d$-dimensional and $d$-partite, with at least two facets;
--   2. $q^{c_1r^2}\le|\mathcal X(1)|\le q^{c_2r^2}$;
--   3. degree at most $q^{Crd}$;
--   4. $\mathcal X$ a $\frac{1}{2d}$-top-link expander;
--   5. $$\lambda_2(P_d^\vee)\le 1-\frac{1}{e\cdot d}.$$
--
--   Fixing $k$ and letting $r\to\infty$, the number of vertices is $q^{\Theta(r^2)}$ while the degree is only $q^{O(rd)}$; together with Theorem 3.1 this yields the vectors of Theorem 1.5.
--
--   **Formalization Note** The complex is built on the vertex type $\mathbb N$ (any countable vertex set gives the same claim). $\lambda_2$ is counted with multiplicity.
--
--   Differences from the source:
--   - reading: q^{Θ(r²)} vertices, degree at most q^{O(rd)} → absolute constants c₁, c₂, C > 0 chosen before k, r and q; reason: the standard meaning of the asymptotic notation
--   - reading: 1/2d-top-link-expander, λ₂(P_d^∨) ≤ 1 − 1/ed → 1/(2d) and 1/(e·d); reason: the usual precedence: 2/(√q − 1) ≤ 1/(2d) iff q ≥ (4d + 1)², and 1/(e·d) is Theorem 2.3's bound at δ = 1/2
--   - encoding: a complex on an unspecified finite vertex set → a complex X : Finset (Finset ℕ); reason: every finite complex is isomorphic to one on ℕ; same instances
--   - generalization: no statement on the number of facets → the conclusion also asserts 2 ≤ |X(d)|; reason: true for the construction, and it makes λ₂(P_d^∨) meaningful; dropping the conjunct gives the printed claim
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Theorem 2.4, p.4

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_SteurerHDX_IsPartite
import Definitions.Def_SteurerHDX_degree
import Definitions.Def_SteurerHDX_IsTopLinkExpander
import Definitions.Def_SteurerHDX_lambdaTwo
import Definitions.Def_SteurerHDX_downUp

namespace SteurerHDX

/-- **Theorem 2.4 (sparse top-link expanders).** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Theorem 2.4, p.4: "Given integers
1 ≤ k < r, let d = 2k + 1. For every prime power q ≥ (4d + 1)², there is a pure d-partite
d-dimensional simplicial complex X with q^{Θ(r²)} vertices, degree at most q^{O(rd)} which is a
1/2d-top-link-expander and the λ₂(P_d^∨) ≤ 1 − 1/ed."

**Formalization Note.** Θ and O are absolute constants c₁, c₂, C, chosen before k, r, q.
"1/2d" is 1/(2d) and "1/ed" is 1/(e·d). The complex is built on the vertex type ℕ (any countable
vertex type gives the same claim). The conclusion also asserts `2 ≤ |X(d)|`, which holds for the
construction and makes λ₂ of the down-up walk meaningful. -/
theorem theorem_2_4 :
    ∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧
    ∀ k r q : ℕ, 1 ≤ k → k < r → IsPrimePow q → (4 * (2 * k + 1) + 1) ^ 2 ≤ q →
    ∃ X : Finset (Finset ℕ),
      IsPure X (2 * k + 1) ∧ IsPartite X (2 * k + 1) ∧ 2 ≤ (faces X (2 * k + 1)).card ∧
      (q : ℝ) ^ (c₁ * (r : ℝ) ^ 2) ≤ ((faces X 1).card : ℝ) ∧
      ((faces X 1).card : ℝ) ≤ (q : ℝ) ^ (c₂ * (r : ℝ) ^ 2) ∧
      (degree X (2 * k + 1) : ℝ) ≤ (q : ℝ) ^ (C * r * (2 * k + 1)) ∧
      IsTopLinkExpander X (2 * k + 1) (1 / (2 * (2 * k + 1))) ∧
      lambdaTwo (downUp X (2 * k + 1)) ≤ 1 - 1 / (Real.exp 1 * (2 * k + 1)) := by sorry

end SteurerHDX
