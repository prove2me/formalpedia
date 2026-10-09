-- Prove2me | Theorems.Thm_QueueingFundamentals_Transient_mm1_transient_bessel
-- name    : QueueingFundamentals.Transient.mm1_transient_bessel
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T08:05:04.368991+00:00
-- url     : https://prove2.me/theorems/12395959-0cb8-4b10-bc7f-7647247fe482
-- title:
--   Eq. (2.75) — the transient M/M/1 law in modified Bessel functions
-- statement:
--   Let $\lambda, \mu > 0$ be the arrival and service rates of an M/M/1 queue, $\rho = \lambda/\mu$, and let the queue start with $N(0) = i$ customers. Write $y = 2t\sqrt{\lambda\mu}$ and let $I_m$ be the modified Bessel function of the first kind, $I_{-m} = I_m$. Define
--
--   $$
--   p_n(t) = e^{-(\lambda+\mu)t}\Big[\rho^{(n-i)/2} I_{n-i}(y) + \rho^{(n-i-1)/2} I_{n+i+1}(y) + (1-\rho)\rho^n \sum_{j=n+i+2}^{\infty} \rho^{-j/2} I_j(y)\Big] \qquad (n \ge 0,\ t \ge 0).
--   $$
--
--   Then:
--
--   1. the series $\sum_{j \ge n+i+2} \rho^{-j/2} I_j(y)$ converges for every $n$ and every $t \ge 0$;
--   2. the functions $p_n$ solve the forward equations (2.72) on $[0,\infty)$:
--   $$ p_n'(t) = -(\lambda+\mu)p_n(t) + \lambda p_{n-1}(t) + \mu p_{n+1}(t)\ (n>0), \qquad p_0'(t) = -\lambda p_0(t) + \mu p_1(t); $$
--   3. $p_n(0) = 1$ if $n = i$ and $p_n(0) = 0$ otherwise;
--   4. $(p_n(t))_{n \ge 0}$ is a probability distribution for every $t \ge 0$;
--   5. every family $(q_n)$ with properties 2–4 coincides with $(p_n)$ on $[0,\infty)$.
--
--   This is the classical closed form (Bailey 1954; Ledermann and Reuter 1954) of the time-dependent distribution of the number in an M/M/1 queue, valid for every traffic intensity $\rho$, not only $\rho < 1$.
--
--   **Formalization Note** The book writes "the final result is" for (2.75); items 2–4 are the existence half and item 5 the uniqueness half of "the solution of (2.72)". The book does not state a uniqueness class; the class chosen here is solutions that are probability distributions at every time. Half-integer powers of $\rho$ are real powers.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.100, Eq. (2.75) (equations (2.72) on p.99; series for I_n on p.101)

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_besselI
import Definitions.Def_QueueingFundamentals_Transient_forwardEquations
import Definitions.Def_QueueingFundamentals_Transient_mm1Transient

namespace QueueingFundamentals.Transient

/-- (2.75): the transient law of the M/M/1 queue started at `N(0) = i`, via modified Bessel
functions. For `λ, μ > 0` and every `i`:
1. the tail series `∑_{j ≥ n+i+2} ρ^{-j/2} I_j(2t√(λμ))` converges for every `n` and `t ≥ 0`;
2. the functions `p_n(t)` of (2.75) solve the forward equations (2.72) on `[0, ∞)`;
3. they satisfy the initial condition `p_n(0) = 1` if `n = i` and `0` otherwise;
4. `p(t)` is a probability distribution for every `t ≥ 0`;
5. they are the only family with properties 2–4. -/
theorem mm1_transient_bessel (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i : ℕ) :
    (∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
        Summable (fun j : ℕ => (lam / mu) ^ (-(((j + n + i + 2 : ℕ) : ℝ)) / 2)
          * besselI (j + n + i + 2) (2 * t * Real.sqrt (lam * mu)))) ∧
      IsForwardSolution (mm1RHS lam mu) (fun n t => mm1Transient lam mu i n t) ∧
      (∀ n : ℕ, mm1Transient lam mu i n 0 = if n = i then 1 else 0) ∧
      IsProbabilityFamily (fun n t => mm1Transient lam mu i n t) ∧
      ∀ q : ℕ → ℝ → ℝ, IsForwardSolution (mm1RHS lam mu) q → IsProbabilityFamily q →
        (∀ n : ℕ, q n 0 = if n = i then 1 else 0) →
        ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → q n t = mm1Transient lam mu i n t := by sorry

end QueueingFundamentals.Transient
