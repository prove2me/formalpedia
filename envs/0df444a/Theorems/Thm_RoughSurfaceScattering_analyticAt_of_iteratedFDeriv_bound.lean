-- Prove2me | Theorems.Thm_RoughSurfaceScattering_analyticAt_of_iteratedFDeriv_bound
-- name    : RoughSurfaceScattering.analyticAt_of_iteratedFDeriv_bound
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T06:02:41.924162+00:00
-- url     : https://prove2.me/theorems/f1638b31-f1f1-42c0-9dca-8b1bea32712d
-- title:
--   Factorial bounds on all derivatives imply real analyticity
-- statement:
--   Let $E$ be a real normed space, $F$ a real Banach space, $x\in E$, and $R,\rho>0$, $M\in\mathbb R$. Suppose $f:E\to F$ is $C^n$ on the ball $B(x,R)$ for every $n$, with
--
--   $$\|D^nf(y)\|\le M\,\frac{n!}{\rho^n}\qquad\text{for all }n\ge0,\ y\in B(x,R).$$
--
--   Then $f$ is real analytic at $x$. More precisely, its Taylor series $\sum_n\frac1{n!}D^nf(x)[h,\dots,h]$ converges to $f(x+h)$ for $|h|<\min(R,\rho/2)$.
--
--   This is the standard bridge from Cauchy-type derivative estimates to analyticity, used for instance to prove that harmonic functions are analytic. Mathlib has Taylor's formula with integral remainder in several variables but not this criterion.
--
--   **Formalization Note** $D^nf$ is Mathlib's `iteratedFDeriv`, with the operator norm on continuous multilinear maps. Smoothness is stated as `ContDiffOn ℝ n` for every natural number $n$.
-- source:
--   Classical criterion for real analyticity via Taylor's formula with remainder; e.g. S. G. Krantz and H. R. Parks, A Primer of Real Analytic Functions, 2nd ed., Proposition 2.2.10; used in L. C. Evans, Partial Differential Equations, §2.2.3, proof of Theorem 10 (analyticity of harmonic functions).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem analyticAt_of_iteratedFDeriv_bound {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (x : E) (R M ρ : ℝ) (hR : 0 < R) (hρ : 0 < ρ)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n f (Metric.ball x R))
    (hb : ∀ n : ℕ, ∀ y ∈ Metric.ball x R,
      ‖iteratedFDeriv ℝ n f y‖ ≤ M * (n.factorial : ℝ) / ρ ^ n) :
    AnalyticAt ℝ f x := by sorry

end RoughSurfaceScattering
