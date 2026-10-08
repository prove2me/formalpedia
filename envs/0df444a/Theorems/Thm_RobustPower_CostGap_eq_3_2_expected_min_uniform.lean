-- Prove2me | Theorems.Thm_RobustPower_CostGap_eq_3_2_expected_min_uniform
-- name    : RobustPower.CostGap.eq_3_2_expected_min_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:12:52.071078+00:00
-- url     : https://prove2.me/theorems/6ebbb5f1-7eb6-44f9-92aa-0e035f711950
-- title:
--   Eq. (3.2), p. 23 — the expected minimum of n independent uniforms on [0, 1] is 1/(n + 1)
-- statement:
--   Let $n\ge1$, let $(\Omega,\mu)$ be a probability space and let $d=(d_1,\dots,d_n):\Omega\to\mathbb R^n$ be a measurable map whose coordinates are independent and each uniformly distributed on $[0,1]$, that is, the law of $d$ under $\mu$ is the product of $n$ copies of the uniform distribution on $[0,1]$. Then
--
--   $$
--   \mathbb E_\mu\bigl[\min\bigl(d_1(\omega),\dots,d_n(\omega)\bigr)\bigr]=\frac{1}{n+1}.
--   $$
--
--   This is the computational core of Theorem 3.1: together with Eq. (3.1) it gives $z_{\mathrm{Stoch}}(b,d)\le1/(n+1)$. The paper calls (3.2) an inequality; it is the equality stated here.
--
--   **Formalization Note** The minimum of the coordinates is written as the infimum over the finite nonempty index set $\{1,\dots,n\}$, which is attained; the hypothesis $n\ge1$ excludes the empty index set.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 23, proof of Theorem 3.1, Eq. (3.2)

import Mathlib

open MeasureTheory

namespace RobustPower.CostGap

/-- Eq. (3.2), p. 23: if the coordinates of `d(ω)` are independent and uniform on `[0, 1]`, then
`E_μ[min(d₁(ω), …, dₙ(ω))] = 1/(n + 1)`. -/
theorem eq_3_2_expected_min_uniform {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d)
    (hlaw : μ.map d = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∫ ω, (⨅ j, d ω j) ∂μ = 1 / ((n : ℝ) + 1) := by sorry

end RobustPower.CostGap
