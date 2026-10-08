-- Prove2me | Theorems.Thm_QueueingFundamentals_Foundations_nonhomogeneous_poisson
-- name    : QueueingFundamentals.Foundations.nonhomogeneous_poisson
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T06:35:38.93365+00:00
-- url     : https://prove2.me/theorems/132febc9-79fa-4f78-b136-74a1d92c43d8
-- title:
--   The nonhomogeneous Poisson law $e^{-m(t)}m(t)^n/n!$ (p.22)
-- statement:
--   Let $\lambda(t)\ge0$ be a rate function, continuous on $[0,\infty)$, and put
--   $$m(t)=\int_0^t\lambda(s)\,ds .$$
--   For real functions $p_n(t)$, $n\ge0$, $t\ge0$, the following are equivalent.
--
--   1. They satisfy the forward equations with time-dependent rate on $t\ge0$ (one-sided derivative at $t=0$),
--   $$\frac{dp_0(t)}{dt}=-\lambda(t)p_0(t),\qquad\frac{dp_n(t)}{dt}=-\lambda(t)p_n(t)+\lambda(t)p_{n-1}(t)\quad(n\ge1),$$
--   with $p_0(0)=1$ and $p_n(0)=0$ for $n>0$.
--   2. For all $n\ge0$ and $t\ge0$,
--   $$p_n(t)=e^{-m(t)}\frac{[m(t)]^n}{n!}.$$
--
--   These are the equations obtained from the axiomatic derivation of §1.7 when the constant rate $\lambda$ is replaced by $\lambda(t)$; the solution is the nonhomogeneous Poisson distribution.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.22, nonhomogeneous Poisson distribution (unnumbered display)

import Mathlib

namespace QueueingFundamentals.Foundations

/-- p.22: with a time-dependent rate `λ(t)`, the unique solution of the forward equations
with `p_0(0) = 1`, `p_n(0) = 0` (`n > 0`) is the nonhomogeneous Poisson law
`p_n(t) = e^{-m(t)} m(t)^n / n!`, `m(t) = ∫_0^t λ(s) ds`. -/
theorem nonhomogeneous_poisson (lam : ℝ → ℝ) (hcont : ContinuousOn lam (Set.Ici 0))
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ lam t) (p : ℕ → ℝ → ℝ) :
    ((∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (p 0) (-lam t * p 0 t) (Set.Ici 0) t) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t →
        HasDerivWithinAt (p n) (-lam t * p n t + lam t * p (n - 1) t) (Set.Ici 0) t) ∧
      p 0 0 = 1 ∧ (∀ n : ℕ, 0 < n → p n 0 = 0)) ↔
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      p n t = Real.exp (-(∫ s in (0 : ℝ)..t, lam s)) * (∫ s in (0 : ℝ)..t, lam s) ^ n /
        (n.factorial : ℝ) := by sorry

end QueueingFundamentals.Foundations
