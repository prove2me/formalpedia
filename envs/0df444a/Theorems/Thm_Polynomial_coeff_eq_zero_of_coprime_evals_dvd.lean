-- Prove2me | Theorems.Thm_Polynomial_coeff_eq_zero_of_coprime_evals_dvd
-- name    : Polynomial.coeff_eq_zero_of_coprime_evals_dvd
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:18.092918+00:00
-- url     : https://prove2.me/theorems/5af374ee-1bad-4da1-acba-f4bdc7ecf3e8
-- title:
--   Four coprime high-power evaluations force bounded coefficients to vanish
-- statement:
--   Let $p∈ℤ[X]$, let $N∈ℕ$, and let $b_0,b_1,b_2,b_3>0$ satisfy $\gcd(b_0,b_1)=1$, $\gcd(b_0b_1,b_2)=1$, and $\gcd(b_0b_1b_2,b_3)=1$. Assume $|[X^i]p|<b_0b_1b_2b_3$ for every $i<N$, and assume $b_j^N\mid p(b_j)$ for $j=0,1,2,3$. Then $$[X^i]p=0\quad\text{for every }i<N.$$ This is the arithmetic reconstruction lemma behind the four-base coefficient certificate.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open Polynomial

theorem Polynomial.coeff_eq_zero_of_coprime_evals_dvd
    (p : ℤ[X]) (N : ℕ) (b₀ b₁ b₂ b₃ : ℤ)
    (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃)
    (hcop₀₁ : IsCoprime b₀ b₁)
    (hcop₂ : IsCoprime (b₀ * b₁) b₂)
    (hcop₃ : IsCoprime (b₀ * b₁ * b₂) b₃)
    (hbound : ∀ i : ℕ, i < N → |p.coeff i| < b₀ * b₁ * b₂ * b₃)
    (heval₀ : b₀ ^ N ∣ p.eval b₀) (heval₁ : b₁ ^ N ∣ p.eval b₁)
    (heval₂ : b₂ ^ N ∣ p.eval b₂) (heval₃ : b₃ ^ N ∣ p.eval b₃) :
    ∀ i : ℕ, i < N → p.coeff i = 0 := by sorry
