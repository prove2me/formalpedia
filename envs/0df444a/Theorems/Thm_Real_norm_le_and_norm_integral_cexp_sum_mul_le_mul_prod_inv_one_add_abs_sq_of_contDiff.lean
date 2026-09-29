-- Prove2me | Theorems.Thm_Real_norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff
-- name    : Real.norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/78227a13-b607-514c-b9b6-91a0ace4fd4e
-- title:
--   Quadratic decay of a compactly supported C^{2r} function and its Fourier transform
-- statement:
--   Let $r$ be a natural number and let $g \colon \mathbb{R}^{r} \to \mathbb{C}$ be a function on $\mathrm{Fin}\,r \to \mathbb{R}$, and let $R, M$ be real numbers with $0 \le R$. Assume $g$ is of class $C^{2r}$ over $\mathbb{R}$ (continuous differentiability of order $(2r : \mathbb{N}_\infty)$); that $g$ vanishes at every $x$ for which some coordinate satisfies $R < |x_k|$; and that for every $n \le 2r$ and every $x$ the norm of the $n$-th iterated Fréchet derivative satisfies $\|D^{n} g(x)\| \le M$. Then, with $C = M\bigl((1+R)^{2r} + (8R)^{r}\bigr)$, two bounds hold simultaneously: first, $\|g(x)\| \le C \prod_{k} \bigl((1+|x_k|)^{-1}\bigr)^{2}$ for all $x \in \mathbb{R}^{r}$; second, for every $\xi \in \mathbb{R}^{r}$ the integral $\int_{\mathbb{R}^{r}} e^{-2\pi i \sum_{k} \xi_k x_k} g(x)\,dx$, taken with respect to the ambient measure on $\mathrm{Fin}\,r \to \mathbb{R}$, has norm at most $C \prod_{k} \bigl((1+|\xi_k|)^{-1}\bigr)^{2}$. Note that the constant $C$ is the same in both bounds and depends linearly on $M$.
--
--   This is the several-variable form of the elementary estimate that a compactly supported $C^{2}$ function and its Fourier transform both decay like $(1+|x|)^{-2}$, here with an explicit constant in terms of the support radius $R$ and a uniform bound $M$ on derivatives up to order $2r$. It supplies the decay needed to control Fourier expansions and Poisson-summation style sums in the analytic part of the development, and is used in the construction of summable majorants for Fourier modes and period integrals of periodic smooth functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Real_norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem Real.norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff
    {r : ℕ} (g : (Fin r → ℝ) → ℂ) (R M : ℝ) (hR : 0 ≤ R)
    (hg : ContDiff ℝ ((2 * r : ℕ) : ℕ∞) g)
    (hsupp : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → g x = 0)
    (hM : ∀ n : ℕ, n ≤ 2 * r → ∀ x : Fin r → ℝ, ‖iteratedFDeriv ℝ n g x‖ ≤ M) :
    (∀ x : Fin r → ℝ, ‖g x‖ ≤ (M * ((1 + R) ^ (2 * r) + (8 * R) ^ r)) * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
    (∀ ξ : Fin r → ℝ,
      ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * g x‖ ≤
        (M * ((1 + R) ^ (2 * r) + (8 * R) ^ r)) * ∏ k, (1 + |ξ k|)⁻¹ ^ 2) := by sorry
