-- Prove2me | Theorems.Thm_Polynomial_Chebyshev_eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero
-- name    : Polynomial.Chebyshev.eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/d7ca6309-8a07-5963-aeda-56ec44a11171
-- title:
--   Completeness of the Chebyshev polynomials Uⱼ on (0,π)
-- statement:
--   Let $g : \mathbb{R} \to \mathbb{C}$ be a function which is continuous on the open interval $(0,\pi)$ and interval integrable, with respect to Lebesgue measure, over the interval with endpoints $0$ and $\pi$. Assume that for every natural number $j$ the integral $\int_0^\pi g(\theta)\, U_j(\cos\theta)\, d\theta$ vanishes, where $U_j$ denotes the Chebyshev polynomial of the second kind of index $j$ (Mathlib's integer-indexed family `Chebyshev.U ℝ` evaluated at the integer $j$), the polynomial being evaluated at the real number $\cos\theta$ and the resulting real value regarded as a complex number; the integral is the interval integral of the complex-valued function $\theta \mapsto g(\theta)\,U_j(\cos\theta)$ from $0$ to $\pi$. The conclusion is that $g(\theta) = 0$ for every $\theta$ in the open interval $(0,\pi)$. No conclusion is asserted at the endpoints $0$ and $\pi$, nor outside $[0,\pi]$, where the hypotheses say nothing about $g$.
--
--   This is the completeness, on $(0,\pi)$, of the system $\{U_j(\cos\theta)\}_{j \ge 0} = \{\sin((j+1)\theta)/\sin\theta\}_{j \ge 0}$: a continuous function orthogonal to all of them vanishes identically there. It is used in the construction of a smooth function with prescribed behaviour attached to a discrete-series pairing for $\mathrm{GL}_2(\mathbb{R})$, where vanishing of all such moments must be upgraded to pointwise vanishing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_Chebyshev_eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero.lean

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Polynomial.Chebyshev.eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero
    (g : ℝ → ℂ) (hg : ContinuousOn g (Set.Ioo 0 Real.pi))
    (hgi : IntervalIntegrable g MeasureTheory.volume 0 Real.pi)
    (hmodes : ∀ j : ℕ,
      ∫ θ in (0 : ℝ)..Real.pi, g θ * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ) = 0) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, g θ = 0 := by sorry
