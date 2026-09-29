-- Prove2me | Theorems.Thm_Polynomial_coeff_countP_roots_isDominant_of_isAlgClosed
-- name    : Polynomial.coeff_countP_roots_isDominant_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/e9c8da0b-d40c-52ec-9d81-fd27386ccaa8
-- title:
--   Coefficients of maximal valuation count roots in the unit disc
-- statement:
--   Let $K$ be a field, algebraically closed, carrying a valuation $v =$ `Valued.v` with values in a linearly ordered commutative group with zero $\Gamma_0$, and let $p \in K[X]$ be a nonzero polynomial. Write $p.\mathrm{roots}$ for the multiset of roots of $p$ in $K$, counted with multiplicity, and set $M$ for the number of its members $\alpha$ with $v(\alpha) \le 1$ and $m$ for the number of its members $\alpha$ with $v(\alpha) < 1$. The assertion is the conjunction of two statements about the coefficients $p_j$ of $p$ (all indices $j$ ranging over $\mathbb{N}$, so that $p_j = 0$ and $v(p_j) = 0$ beyond the degree). First: $v(p_j) \le v(p_M)$ for every $j$, and $v(p_j) < v(p_M)$ whenever $j > M$. Second: $v(p_j) \le v(p_m)$ for every $j$, and $v(p_j) < v(p_m)$ whenever $j < m$. Thus $M$ is the largest and $m$ the smallest index at which the valuation of the coefficients of $p$ attains its maximum.
--
--   This identifies the horizontal segment of the Newton polygon of $p$ at radius $1$: its abscissae run from $m$ to $M$, so the Gauss norm of $p$ on the closed unit disc is $\max_j v(p_j)$ and the number of roots in the closed (resp. open) unit disc is read off from the extremal index at which this maximum occurs. It is used in the analysis of holomorphic functions on subsets of the non-archimedean line, for the construction of multiplicative inverses of nowhere-vanishing functions and for the finiteness of zero sets on discs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_coeff_countP_roots_isDominant_of_isAlgClosed.lean

import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Polynomial.coeff_countP_roots_isDominant_of_isAlgClosed
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (p : Polynomial K) (hp : p ≠ 0) :
    ((∀ j : ℕ, Valued.v (p.coeff j) ≤ Valued.v (p.coeff (p.roots.countP fun α => Valued.v α ≤ 1))) ∧
      ∀ j : ℕ, (p.roots.countP fun α => Valued.v α ≤ 1) < j →
        Valued.v (p.coeff j) < Valued.v (p.coeff (p.roots.countP fun α => Valued.v α ≤ 1))) ∧
    ((∀ j : ℕ, Valued.v (p.coeff j) ≤ Valued.v (p.coeff (p.roots.countP fun α => Valued.v α < 1))) ∧
      ∀ j : ℕ, j < (p.roots.countP fun α => Valued.v α < 1) →
        Valued.v (p.coeff j) < Valued.v (p.coeff (p.roots.countP fun α => Valued.v α < 1))) := by sorry
