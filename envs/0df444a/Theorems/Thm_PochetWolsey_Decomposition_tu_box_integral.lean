-- Prove2me | Theorems.Thm_PochetWolsey_Decomposition_tu_box_integral
-- name    : PochetWolsey.Decomposition.tu_box_integral
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:44.923294+00:00
-- url     : https://prove2.me/theorems/6ac5bef5-037f-4833-86fe-82ff87873b7b
-- title:
--   Theorem 6.7 — integrality of a TU polyhedron with integer bounds
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ be totally unimodular, and let $b\in\mathbb Z^m$ and $l,h\in\mathbb Z^n$. If
--   $$
--   P=\{x\in\mathbb R^n:Ax\le b,\ l\le x\le h\}
--   $$
--   is nonempty, every extreme point of $P$ has integer coordinates. Thus $P$ is integral in the terminology of Section 6.4. This companion result supplies an integrality criterion for subsequent formulation arguments.
--
--   **Formalization Note** The coordinate bounds are arbitrary integers, including negative values. Nonemptiness is explicit; no nonnegativity restriction, integrality of arbitrary feasible points, or integrality conclusion is assumed.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, DOI 10.1007/0-387-33477-7, p. 204 (PDF 218), Theorem 6.7; definition of integral polyhedron, p. 203

import Mathlib

namespace PochetWolsey.Decomposition

theorem tu_box_integral {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℤ) (l h : Fin n → ℤ) (hA : A.IsTotallyUnimodular) :
    let P : Set (Fin n → ℝ) := {x | (∀ i, (∑ j, A i j * x j) ≤ (b i : ℝ)) ∧
      (∀ j, (l j : ℝ) ≤ x j) ∧ (∀ j, x j ≤ (h j : ℝ))}
    P.Nonempty → ∀ x ∈ Set.extremePoints ℝ P, ∀ j, ∃ z : ℤ, x j = (z : ℝ) := by sorry

end PochetWolsey.Decomposition
