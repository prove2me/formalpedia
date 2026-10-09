-- Prove2me | Theorems.Thm_ToddKK14_Diameter_theorem_1
-- name    : ToddKK14.Diameter.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:37.329347+00:00
-- url     : https://prove2.me/theorems/0dd3f83e-87b1-467c-b056-927a0cd219c0
-- title:
--   Theorem 1 — every polyhedron in ℝ^d cut out by n ≥ d inequalities, bounded or not, has graph diameter at most (n − d)^{log₂ d}
-- statement:
--   A **polyhedron** $P\subseteq\mathbb R^d$ is an intersection of finitely many half-spaces. A **vertex** of $P$ is a point $v$ such that $P\cap H=\{v\}$ for some half-space $H$; two vertices $v\ne w$ are **adjacent** if $P\cap H=[v,w]$ for some half-space $H$. The distance $\rho_P(v,w)$ is the least length of a path of adjacent vertices from $v$ to $w$, the **diameter** $\delta(P)$ is the largest such distance, and $\Delta(d,n)$ is the largest diameter of a $d$-dimensional polyhedron with $n$ facets, **bounded or not**.
--
--   **Theorem 1 (Todd).** For $1\le d\le n$,
--
--   $$
--   \Delta(d,n)\;\le\;(n-d)^{\log d}, \qquad\text{with } \Delta(1,1)=0,
--   $$
--
--   where $\log$ is the logarithm to base 2.
--
--   Concretely: let $1\le d\le n$ and let $P=\{x\in\mathbb R^d:\langle a_i,x\rangle\le b_i,\ i=1,\dots,n\}$ be any polyhedron cut out by $n$ linear inequalities, bounded or not. Then the vertex–edge graph of $P$ is connected and any two vertices of $P$ are joined by a path of at most $\lfloor (n-d)^{\log_2 d}\rfloor$ edges; and if $d=n=1$, $P$ has at most one vertex.
--
--   The bound improves the Kalai–Kleitman bound $n^{\log d+2}$ (1992), agrees with the Hirsch quantity $n-d$ for $d\le 2$, and is invariant under linear-programming duality, since $(n-d)^{\log d}=d^{\log(n-d)}$.
--
--   **Formalization Note** The statement uses the **inequality reading** of $\Delta(d,n)\le B$: for all $a:\{1..n\}\to\mathbb R^d$ and $b$, the polyhedron `Hpoly a b` satisfies `DiamLE … B` (any two extreme points are joined by a walk of exactly $B$ steps, each step staying put or crossing an edge, so connectivity is included). This is equivalent to the paper's statement: a $(d,n)$-polyhedron is the `Hpoly` of its $n$ facet inequalities, and conversely an `Hpoly` with $n$ rows of dimension $d'<d$ has $n'$ facets with $n'-d'\le n-d$, so the bound for $(d',n')$ is at most the bound for $(d,n)$. **No boundedness, nonemptiness, full-dimensionality or nonzero-row hypothesis is imposed.** The logarithm is `Real.logb 2`, the power is the real power, and since distances are natural numbers the bound is its floor. The second conjunct is the paper's "with $\Delta(1,1)=0$": it is needed because $0^0=1$ in `Real.rpow`, so the first conjunct gives only the bound $1$ at $d=n=1$. The bounded case with $d\ge 3$ is the published `Hirsch.todd_bound`; this theorem is its extension to all polyhedra.
-- source:
--   Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, arXiv:1402.3579v2, p. 2, §2, Theorem 1

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace ToddKK14.Diameter

open Hirsch

/-- Todd (2014), p. 2, Theorem 1: "For 1 ≤ d ≤ n, ∆(d, n) ≤ (n − d)^{log(d)}, with ∆(1, 1) = 0",
logarithms to base 2. Every polyhedron `Hpoly a b` in `ℝ^d` cut out by `n` linear inequalities,
bounded or not, has a connected vertex–edge graph of diameter at most `⌊(n − d)^{log₂ d}⌋`; and when
`d = n = 1` the diameter is `0`. -/
theorem theorem_1 (d n : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    DiamLE (Hpoly a b) ⌊((n : ℝ) - d) ^ Real.logb 2 d⌋₊ ∧
      (d = 1 → n = 1 → DiamLE (Hpoly a b) 0) := by sorry

end ToddKK14.Diameter
