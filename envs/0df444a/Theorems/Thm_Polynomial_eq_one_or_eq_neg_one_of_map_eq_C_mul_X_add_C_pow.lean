-- Prove2me | Theorems.Thm_Polynomial_eq_one_or_eq_neg_one_of_map_eq_C_mul_X_add_C_pow
-- name    : Polynomial.eq_one_or_eq_neg_one_of_map_eq_C_mul_X_add_C_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/e3d1c165-bab5-51cb-87ac-dc2bad15ac12
-- title:
--   Rationality forces r=±1 for ℓ-adic linear factors
-- statement:
--   Let $\ell$ be a prime, let $g$ be a natural number with $1 \le g$, let $P \in \mathbb{Q}[X]$, let $a \in \mathbb{Q}$ satisfy $a = 1$ or $a = -1$, and assume the constant coefficient $P.\mathrm{coeff}\,0$ is $1$ or $-1$. Let $r \in \mathbb{Q}_{\ell}$ and suppose that the image of $P$ under the coefficientwise extension of the structure map $\mathbb{Q} \to \mathbb{Q}_{\ell}$ equals $C(a) \cdot (X + C\,r)^{g}$ in $\mathbb{Q}_{\ell}[X]$, where $a$ is viewed in $\mathbb{Q}_{\ell}$ and $C$ denotes the constant-polynomial embedding. Then $r = 1$ or $r = -1$ (as elements of $\mathbb{Q}_{\ell}$). Note that $P$ is not assumed to be monic, nor of degree $g$: the displayed factorisation over $\mathbb{Q}_{\ell}$ is the only link between $P$, $a$, $g$ and $r$, and it forces $P$ to be $a(X+r)^g$ with $r$ the image of a rational number.
--
--   An elementary rigidity statement: a rational polynomial whose base change to $\mathbb{Q}_{\ell}$ is $\pm(X+r)^{g}$ with constant term $\pm 1$ can only have $r = \pm 1$, the point being that the coefficient of $X^{g-1}$ already pins $r$ down to a rational number, so that $r^{g} = \pm 1$ may be solved in $\mathbb{Q}$. It is used in the Čerednik–Drinfeld/fake elliptic curve part of the development, in the analysis of the characteristic polynomial of an endomorphism compatible with the Rosati involution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_eq_one_or_eq_neg_one_of_map_eq_C_mul_X_add_C_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Polynomial.eq_one_or_eq_neg_one_of_map_eq_C_mul_X_add_C_pow
    (ℓ : ℕ) [Fact ℓ.Prime] (g : ℕ) (hg : 1 ≤ g) (P : ℚ[X]) (a : ℚ) (ha : a = 1 ∨ a = -1)
    (h0 : P.coeff 0 = 1 ∨ P.coeff 0 = -1) (r : ℚ_[ℓ])
    (hP : P.map (algebraMap ℚ ℚ_[ℓ]) = C (algebraMap ℚ ℚ_[ℓ] a) * (X + C r) ^ g) :
    r = 1 ∨ r = -1 := by sorry
