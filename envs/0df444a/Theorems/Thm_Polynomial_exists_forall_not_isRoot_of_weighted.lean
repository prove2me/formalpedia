-- Prove2me | Theorems.Thm_Polynomial_exists_forall_not_isRoot_of_weighted
-- name    : Polynomial.exists_forall_not_isRoot_of_weighted
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/697d2d25-5895-5fd1-97b5-ae398382c8c6
-- title:
--   Rootless integral specialisations of a weighted polynomial
-- statement:
--   Let $n,w$ be natural numbers and let $F \in \mathbb{Q}[t][x]$ be a polynomial in $x$ (the outer variable) with coefficients $F_k :=$ `F.coeff k` in $\mathbb{Q}[t]$, subject to: $\deg_x F \le n$; the weight condition that $[t^j]F_k = 0$ whenever $j > w\,(n-k)$ (truncated subtraction), so that $\deg F_k \le w(n-k)$ for $k \le n$ and $F_n$ is the constant $c := [t^0]F_n$; the nondegeneracy $c \neq 0$; the separability, as an element of $\mathbb{Q}[x]$, of the weighted leading form $\sum_{k=0}^{n} \bigl([t^{w(n-k)}]F_k\bigr)\,x^{k}$; and the hypothesis that $F$ has no root in the polynomial ring, i.e. substituting any $g \in \mathbb{Q}[t]$ for $x$ gives $F(g) \neq 0$ in $\mathbb{Q}[t]$. Then for every nonzero natural number $M$ and every natural number $m_0$ there exists $m \ge m_0$ such that the specialisation of $F$ at $t = Mm$, obtained by applying $\mathbb{Q}[t] \to \mathbb{Q}$, $t \mapsto Mm$, to the coefficients, has no rational root: no $x \in \mathbb{Q}$ with $F(Mm,x) = 0$.
--
--   This is an elementary, Dörge-style case of Hilbert's irreducibility theorem: a one-parameter family with separable behaviour at $t = \infty$ and no root in $\mathbb{Q}[t]$ has rootless fibres at integers in any prescribed progression $t \equiv 0 \pmod M$ (the conclusion as stated gives one such $m$ beyond each bound $m_0$, hence infinitely many). It is applied in [`WeierstrassCurve.exists_forall_not_isRoot_Psi3_specialization`](thm.html#WeierstrassCurve.exists_forall_not_isRoot_Psi3_specialization) to the $3$-division polynomial of a one-parameter family of elliptic curves, producing members with prescribed congruence conditions whose mod-$3$ representation has no rational point of order $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_exists_forall_not_isRoot_of_weighted.lean

import Mathlib.FieldTheory.Separable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem Polynomial.exists_forall_not_isRoot_of_weighted (n w : ℕ) (F : Polynomial (Polynomial ℚ)) (hF : F.natDegree ≤ n) (hwt : ∀ k j : ℕ, w * (n - k) < j → (F.coeff k).coeff j = 0) (hlead : (F.coeff n).coeff 0 ≠ 0) (hsep : (∑ k ∈ Finset.range (n + 1), C ((F.coeff k).coeff (w * (n - k))) * X ^ k : Polynomial ℚ).Separable) (hroot : ∀ g : Polynomial ℚ, F.eval g ≠ 0) (M : ℕ) (hM : M ≠ 0) (m₀ : ℕ) : ∃ m : ℕ, m₀ ≤ m ∧ ∀ x : ℚ, ¬ (F.map (Polynomial.evalRingHom ((M : ℚ) * m))).IsRoot x := by sorry
