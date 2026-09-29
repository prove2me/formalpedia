-- Prove2me | Theorems.Thm_Polynomial_map_eq_C_mul_X_add_C_pow_of_forall_dvd_eval
-- name    : Polynomial.map_eq_C_mul_X_add_C_pow_of_forall_dvd_eval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/5e367005-4aa3-5ce7-b196-2d3391b4856f
-- title:
--   Rational polynomial with ℓ-adically divisible values is a_g(X+c)^g
-- statement:
--   Let $\ell$ be a prime and $g$ a natural number, and let $P \in \mathbb{Q}[X]$ be a polynomial whose natural degree is at most $g$. Suppose given a function $\chi : \mathbb{N} \to \mathbb{Z}$ such that $P(m) = \chi(m)$ in $\mathbb{Q}$ for every natural number $m$, so that $P$ takes integer values at the natural numbers, and let $c \in \mathbb{Z}_\ell$. Assume that for every natural number $m$ with $m + c \neq 0$ in $\mathbb{Z}_\ell$ one has the divisibility $(m + c)^g \mid \chi(m)$ in $\mathbb{Z}_\ell$, where $m$ and $\chi(m)$ are read in $\mathbb{Z}_\ell$ via the canonical maps. The conclusion is an identity in $\mathbb{Q}_\ell[X]$: the image of $P$ under the coefficientwise map induced by the algebra map $\mathbb{Q} \to \mathbb{Q}_\ell$ equals the constant polynomial on the image of the coefficient of $X^g$ in $P$, times $(X + c)^g$, the constant $c$ being viewed in $\mathbb{Q}_\ell$. No lower bound on $g$ and no normalisation of the leading coefficient is assumed; for $g = 0$ the assertion is trivial, and $P = 0$ is permitted.
--
--   An integrality-and-divisibility rigidity statement for integer-valued rational polynomials, proved by $\ell$-adic estimates on the values $P(m)$ as $m$ approaches $-c$ in $\mathbb{Z}_\ell$. It is used in the construction of fake elliptic curves in the Čerednik–Drinfeld part of the development, where a polynomial arising from a degree or trace computation is forced into the shape $a_g(X+c)^g$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_map_eq_C_mul_X_add_C_pow_of_forall_dvd_eval.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Polynomial.map_eq_C_mul_X_add_C_pow_of_forall_dvd_eval
    (ℓ : ℕ) [Fact ℓ.Prime] (g : ℕ) (P : ℚ[X]) (hdeg : P.natDegree ≤ g)
    (χ : ℕ → ℤ) (hχ : ∀ m : ℕ, P.eval (m : ℚ) = (χ m : ℚ)) (c : ℤ_[ℓ])
    (hval : ∀ m : ℕ, (m : ℤ_[ℓ]) + c ≠ 0 → ((m : ℤ_[ℓ]) + c) ^ g ∣ (χ m : ℤ_[ℓ])) :
    P.map (algebraMap ℚ ℚ_[ℓ]) =
      C (algebraMap ℚ ℚ_[ℓ] (P.coeff g)) * (X + C (c : ℚ_[ℓ])) ^ g := by sorry
