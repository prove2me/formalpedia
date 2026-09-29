-- Prove2me | Theorems.Thm_Polynomial_exists_approximants_at_infty
-- name    : Polynomial.exists_approximants_at_infty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/c55366a6-bcd0-5a1d-a518-b6d7749b6864
-- title:
--   Truncated factorisation at infinity of a weighted polynomial
-- statement:
--   Let $K$ be a field, let $n,w$ be natural numbers, and let $F \in K[t][x]$ (written as a polynomial in $x$ whose coefficients `F.coeff k` lie in $K[t]$) satisfy: the degree of $F$ in $x$ is at most $n$; for all $k,j$ with $j > w\,(n-k)$ (truncated subtraction) the coefficient of $t^j$ in `F.coeff k` vanishes, i.e. $\deg_t(\mathtt{F.coeff }k) \le w(n-k)$; and `F.coeff n` is the constant polynomial $C c$ for a given $c \in K$. Form the top weighted part $F_\infty = \sum_{k=0}^{n} C\big([t^{w(n-k)}]\,\mathtt{F.coeff }k\big)\,X^k \in K[X]$. Let $r : \mathrm{Fin}\,n \to K$ be injective and assume that each $r(i)$ is a root of $F_\infty$ at which the derivative of $F_\infty$ does not vanish. The conclusion is the existence of $P : \mathrm{Fin}\,n \to K[t]$ with $\deg P(i) \le w$ and $[t^w]P(i) = r(i)$ for every $i$, such that the remainder $F - C(C c)\prod_i (X - C(P(i)))$ has vanishing coefficient of $t^j x^k$ whenever $w\,(n-k) \le j + w$; in particular its $x^{n-1}$-part and all its $x^k$-parts with $k \ge n-1$ vanish identically, and for $k < n-1$ its $t$-degree in the $x^k$-part is at most $w(n-k)-w-1$.
--
--   This is the elementary Hensel-type statement at the place $t = \infty$: simple roots of the top weighted form of a polynomial of weighted degree $\le nw$ (weights $\mathrm{wt}(t)=1$, $\mathrm{wt}(x)=w$) lift to order-$(w+1)$ polynomial approximants of the $n$ branches, giving a factorisation of $F$ into linear factors in $x$ up to a remainder of strictly smaller weighted degree. It is used by [`Polynomial.exists_forall_not_isRoot_of_weighted`](thm.html#Polynomial.exists_forall_not_isRoot_of_weighted), in the Dörge-style specialisation argument for Hilbert irreducibility.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_exists_approximants_at_infty.lean

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem Polynomial.exists_approximants_at_infty {K : Type*} [Field K] (n w : ℕ) (F : Polynomial (Polynomial K)) (hF : F.natDegree ≤ n) (hwt : ∀ k j : ℕ, w * (n - k) < j → (F.coeff k).coeff j = 0) (c : K) (hlead : F.coeff n = C c) (r : Fin n → K) (hr : Function.Injective r) (h0 : ∀ i, (∑ k ∈ Finset.range (n + 1), C ((F.coeff k).coeff (w * (n - k))) * X ^ k).eval (r i) = 0) (h1 : ∀ i, (derivative (∑ k ∈ Finset.range (n + 1), C ((F.coeff k).coeff (w * (n - k))) * X ^ k)).eval (r i) ≠ 0) : ∃ P : Fin n → Polynomial K, (∀ i, (P i).natDegree ≤ w) ∧ (∀ i, (P i).coeff w = r i) ∧ ∀ k j : ℕ, w * (n - k) ≤ j + w → ((F - C (C c) * ∏ i, (X - C (P i))).coeff k).coeff j = 0 := by sorry
