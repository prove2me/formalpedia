-- Prove2me | Theorems.Thm_ToddKK14_Diameter_facet_step
-- name    : ToddKK14.Diameter.facet_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:38.563888+00:00
-- url     : https://prove2.me/theorems/79607ef4-e217-48ae-a732-8f2eba8a9ccc
-- title:
--   §2, p. 3, proof of Theorem 1 — if n < 2d, any two vertices share a facet, so δ(P) ≤ ∆(d − 1, n − 1)
-- statement:
--   Let $d\ge 1$, let $n=k+1<2d$, and let $P=\{x\in\mathbb R^d : \langle a_i,x\rangle\le b_i,\ i=1,\dots,n\}$ be a polyhedron, bounded or not, whose normals $a_i$ are all nonzero. Let $B$ be a natural number such that every polyhedron in $\mathbb R^{d-1}$ cut out by $k=n-1$ linear inequalities has graph diameter at most $B$ (that is, $\Delta(d-1,n-1)\le B$). Then
--
--   $$
--   \delta(P)\le B .
--   $$
--
--   In the paper: when $n<2d$, any two vertices lie on a common facet (each vertex lies on at least $d$ of the $n$ facets), "so their distance is at most $\Delta(d-1,n-1)$". This dispatches the case $n<2d$ of the induction proving Theorem 1, before the general step for $n\ge 2d$.
--
--   **Formalization Note** $\Delta(d-1,n-1)\le B$ is the inequality reading: the hypothesis quantifies over all `Hpoly a' b'` in $\mathbb R^{d-1}$ with $k$ rows, bounded or not. The rows are indexed by `Fin (k + 1)`, as in the referenced `KalaiKleitman92.Diameter.facet_walk`, so that milestone applies directly; `hk : k + 1 < 2 * d` forces $d\ge 1$, so $\mathbb R^{d-1}$ (`Fin (d - 1)`) is the true facet dimension. The hypothesis that all rows are nonzero is a disclosed addition: a zero row $\langle 0,x\rangle\le 0$ is tight everywhere, so sharing it would not mean sharing a facet. A $(d,n)$-polyhedron given by its facet inequalities has nonzero rows, so this loses nothing.
-- source:
--   Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, arXiv:1402.3579v2, p. 3, §2, proof of Theorem 1, sentence "Also, the result clearly holds by induction if n < 2d"

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace ToddKK14.Diameter

open Hirsch

/-- Todd (2014), p. 3, proof of Theorem 1: "the result clearly holds by induction if n < 2d, since
then any two vertices lie on a common facet, so their distance is at most ∆(d − 1, n − 1)". Let
`P = Hpoly a b ⊆ ℝ^d` be cut out by `n = k + 1 < 2d` nonzero inequalities, bounded or not. If every
polyhedron in `ℝ^(d-1)` cut out by `k` inequalities has graph diameter at most `B`, then so does
`P`. -/
theorem facet_step (d k : ℕ) (hk : k + 1 < 2 * d)
    (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d)) (b : Fin (k + 1) → ℝ) (hane : ∀ i, a i ≠ 0)
    (B : ℕ)
    (IH : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      DiamLE (Hpoly a' b') B) :
    DiamLE (Hpoly a b) B := by sorry

end ToddKK14.Diameter
