-- Prove2me | Theorems.Thm_Polynomial_abs_coeff_binomial_product_le_exp
-- name    : Polynomial.abs_coeff_binomial_product_le_exp
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:18.277609+00:00
-- url     : https://prove2.me/theorems/5d51464c-9660-451c-89cd-3176983ef8d3
-- title:
--   Coefficients of products of binomials satisfy an exponential majorant
-- statement:
--   Let $0≤q≤1$, let $e_1,…,e_r$ be a finite list of natural numbers, and let $s,n∈ℕ$. For $P(X)=X^s\prod_{j=1}^{r}(1-X^{e_j})∈ℤ[X]$, $$|[X^n]P|q^n≤\exp\left(\sum_{j=1}^{r}q^{e_j}\right).$$ This analytic bound controls the size of the relation-polynomial coefficients.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open Polynomial

theorem Polynomial.abs_coeff_binomial_product_le_exp
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (es : List ℕ) (s n : ℕ) :
    |((X ^ s * (es.map fun e => (1 - X ^ e : ℤ[X])).prod).coeff n : ℝ)| * q ^ n ≤
      Real.exp ((es.map fun e => q ^ e).sum) := by sorry
