-- Prove2me | Theorems.Thm_Real_tsum_comp_add_intCast_eq_tsum_integral_mul_cexp
-- name    : Real.tsum_comp_add_intCast_eq_tsum_integral_mul_cexp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/c823bd46-3283-5f23-91b5-b64a3f183667
-- title:
--   Poisson summation on ℝᵈ for the lattice ℤᵈ
-- statement:
--   Let $d$ be a finite index type and let $f$ be a continuous map from $d \to \mathbb{R}$ (the function type, carrying the supremum norm and the product Lebesgue measure) to $\mathbb{C}$. Two summability hypotheses are imposed. First, for every compact subset $K$ of $d \to \mathbb{R}$, the family indexed by $n : d \to \mathbb{Z}$ of the norms of the restrictions to $K$ of the translated maps $y \mapsto f\bigl(y + (n_i)_i\bigr)$ is summable; each such norm is the supremum over $K$ of $\lvert f(y+n) \rvert$. Second, the family of integrals
--   $$\hat f(n) \;=\; \int_{d \to \mathbb{R}} e^{-2\pi i \left(\sum_i n_i y_i\right)} f(y)\,dy, \qquad n : d \to \mathbb{Z},$$
--   is summable in $\mathbb{C}$, the pairing $\sum_i n_i y_i$ being formed in $\mathbb{R}$ and then coerced to $\mathbb{C}$. The conclusion is that for every $x : d \to \mathbb{R}$,
--   $$\sum_{n : d \to \mathbb{Z}} f\bigl(x + (n_i)_i\bigr) \;=\; \sum_{n : d \to \mathbb{Z}} \hat f(n)\, e^{2\pi i \left(\sum_i n_i x_i\right)},$$
--   both sides being unconditional sums over $d \to \mathbb{Z}$.
--
--   This is the Poisson summation formula in $d$ variables for the standard lattice $\mathbb{Z}^d \subset \mathbb{R}^d$, in the continuous form with locally uniformly summable periodisation and summable Fourier coefficients; it is the several-variable counterpart of the one-dimensional statement available for functions on $\mathbb{R}$. It is used to obtain a summation formula for translates by integer vectors in the first variable, expressed through Fourier integrals, in [`MeasureTheory.hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable`](thm.html#MeasureTheory.hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Real_tsum_comp_add_intCast_eq_tsum_integral_mul_cexp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory TopologicalSpace

theorem Real.tsum_comp_add_intCast_eq_tsum_integral_mul_cexp
    {d : Type*} [Fintype d] (f : C(d → ℝ, ℂ))
    (h_norm : ∀ K : Compacts (d → ℝ),
      Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (fun i => (n i : ℝ)))).restrict K‖)
    (h_sum : Summable fun n : d → ℤ =>
      ∫ y : d → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * y i : ℝ) : ℂ))) * f y)
    (x : d → ℝ) :
    ∑' n : d → ℤ, f (x + fun i => (n i : ℝ)) =
      ∑' n : d → ℤ, (∫ y : d → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * y i : ℝ) : ℂ))) * f y) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * x i : ℝ) : ℂ)) := by sorry
