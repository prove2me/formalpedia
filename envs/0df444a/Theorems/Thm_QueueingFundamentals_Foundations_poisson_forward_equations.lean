-- Prove2me | Theorems.Thm_QueueingFundamentals_Foundations_poisson_forward_equations
-- name    : QueueingFundamentals.Foundations.poisson_forward_equations
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T06:35:19.382989+00:00
-- url     : https://prove2.me/theorems/8ebc9877-e8a4-4fc1-b6b1-fe16484ced68
-- title:
--   Eqs. (1.11)–(1.14) — the Poisson probabilities are the unique solution of the differential-difference equations
-- statement:
--   Let $\lambda>0$ and let $p_n(t)$, $n=0,1,2,\dots$, $t\ge0$, be real functions. The following are equivalent.
--
--   1. The functions satisfy the differential-difference equations of the Poisson process on $t\ge0$ (one-sided derivative at $t=0$),
--   $$\frac{dp_0(t)}{dt}=-\lambda p_0(t),\qquad \frac{dp_n(t)}{dt}=-\lambda p_n(t)+\lambda p_{n-1}(t)\quad(n\ge1),$$
--   together with the initial conditions $p_0(0)=1$ and $p_n(0)=0$ for $n>0$.
--   2. For all $n\ge0$ and $t\ge0$,
--   $$p_n(t)=\frac{(\lambda t)^n}{n!}e^{-\lambda t}.$$
--
--   So the Poisson probabilities (1.14) solve (1.11)–(1.12) with these initial conditions, and they are the only solution. This is the step (left as Problem 1.13 in the book) that turns the derivation of §1.7 into the Poisson law of the number of arrivals.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.17, Eqs. (1.11)–(1.14)

import Mathlib

namespace QueueingFundamentals.Foundations

/-- Eqs. (1.11)–(1.14): the unique solution of the Poisson differential-difference equations
with `p_0(0) = 1`, `p_n(0) = 0` (`n > 0`) is `p_n(t) = (λt)^n e^{-λt} / n!` on `t ≥ 0`. -/
theorem poisson_forward_equations (lam : ℝ) (hlam : 0 < lam) (p : ℕ → ℝ → ℝ) :
    ((∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (p 0) (-lam * p 0 t) (Set.Ici 0) t) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t →
        HasDerivWithinAt (p n) (-lam * p n t + lam * p (n - 1) t) (Set.Ici 0) t) ∧
      p 0 0 = 1 ∧ (∀ n : ℕ, 0 < n → p n 0 = 0)) ↔
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      p n t = (lam * t) ^ n / (n.factorial : ℝ) * Real.exp (-(lam * t)) := by sorry

end QueueingFundamentals.Foundations
