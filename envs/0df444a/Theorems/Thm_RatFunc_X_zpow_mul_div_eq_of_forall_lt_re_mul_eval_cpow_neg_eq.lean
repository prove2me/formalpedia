-- Prove2me | Theorems.Thm_RatFunc_X_zpow_mul_div_eq_of_forall_lt_re_mul_eval_cpow_neg_eq
-- name    : RatFunc.X_zpow_mul_div_eq_of_forall_lt_re_mul_eval_cpow_neg_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/4173a59e-1f82-594c-a0be-d0052636e1fe
-- title:
--   Uniqueness in ℂ(X) of a Dirichlet-series rational form
-- statement:
--   Let $N$ be a natural number with $N>1$, let $\sigma$ be a real number and let $f:\mathbb{C}\to\mathbb{C}$ be an arbitrary function. Let $P,Q,P',Q'\in\mathbb{C}[X]$ be polynomials with $Q\neq 0$ and $Q'\neq 0$, and let $m,m'$ be integers. Assume that for every $s\in\mathbb{C}$ with $\operatorname{Re} s>\sigma$ one has $f(s)\,Q(N^{-s}) = N^{ms}\,P(N^{-s})$, and likewise that for every such $s$ one has $f(s)\,Q'(N^{-s}) = N^{m's}\,P'(N^{-s})$, where the powers of $N$ are complex powers of the cast of $N$ and $P,Q,P',Q'$ are evaluated at $N^{-s}$. The conclusion is an identity in the field of rational functions $\mathbb{C}(X)$: the product of the integer power $X^{-m}$ with the quotient of the images of $P$ and $Q$ under the algebra map $\mathbb{C}[X]\to\mathbb{C}(X)$ equals the product of $X^{-m'}$ with the corresponding quotient built from $P'$ and $Q'$. No analyticity, continuity or growth assumption is imposed on $f$.
--
--   This is the uniqueness statement for the representation of a function on a right half-plane in the rational form $N^{ms}P(N^{-s})/Q(N^{-s})$: such data determine a single well-defined element of $\mathbb{C}(X)$ in the variable $X=N^{-s}$. It is used in the Rankin–Selberg part of the Langlands–Tunnell input, where local zeta integrals converging only on a half-plane are to be regarded as rational functions of $N^{-s}$, for instance in the treatment of torus zeta integrals and their functional equations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RatFunc_X_zpow_mul_div_eq_of_forall_lt_re_mul_eval_cpow_neg_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem RatFunc.X_zpow_mul_div_eq_of_forall_lt_re_mul_eval_cpow_neg_eq
    (N : ℕ) (hN : 1 < N) (σ : ℝ) (f : ℂ → ℂ)
    (P Q P' Q' : Polynomial ℂ) (m m' : ℤ) (hQ : Q ≠ 0) (hQ' : Q' ≠ 0)
    (h : ∀ s : ℂ, σ < s.re → f s * Q.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)))
    (h' : ∀ s : ℂ, σ < s.re → f s * Q'.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s))) :
    (RatFunc.X : RatFunc ℂ) ^ (-m) * (algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) =
      (RatFunc.X : RatFunc ℂ) ^ (-m') * (algebraMap (Polynomial ℂ) (RatFunc ℂ) P' / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q') := by sorry
