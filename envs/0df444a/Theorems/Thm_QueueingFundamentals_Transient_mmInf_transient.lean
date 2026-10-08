-- Prove2me | Theorems.Thm_QueueingFundamentals_Transient_mmInf_transient
-- name    : QueueingFundamentals.Transient.mmInf_transient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T07:51:14.985245+00:00
-- url     : https://prove2.me/theorems/49605ef0-790b-43c6-8155-2c933f757ce7
-- title:
--   Eq. (2.77) — the transient law of the M/M/∞ queue
-- statement:
--   Let $\lambda > 0$ be the arrival rate and $\mu > 0$ the per-customer service rate of an M/M/∞ queue that starts empty, $N(0) = 0$. Put $a(t) = (1 - e^{-\mu t})\lambda/\mu$ and
--
--   $$
--   p_n(t) = \frac{a(t)^n}{n!} e^{-a(t)} \qquad (n \ge 0).
--   $$
--
--   Then:
--
--   1. the $p_n$ solve the forward equations (2.76) on $[0,\infty)$:
--   $$ p_n'(t) = -(\lambda+n\mu)p_n(t) + \lambda p_{n-1}(t) + (n+1)\mu p_{n+1}(t)\ (n>0), \qquad p_0'(t) = -\lambda p_0(t) + \mu p_1(t); $$
--   2. $p_n(0) = 1$ if $n = 0$ and $0$ otherwise;
--   3. $(p_n(t))_n$ is a probability distribution for every $t \ge 0$;
--   4. for $t \ge 0$ and complex $z$ with $|z| \le 1$, the generating function is
--   $$ P(z,t) = \sum_{n=0}^{\infty} p_n(t) z^n = \exp\Big((z-1)(1-e^{-\mu t})\frac{\lambda}{\mu}\Big); $$
--   5. every probability solution of (2.76) with the same initial condition coincides with $(p_n)$ on $[0,\infty)$.
--
--   Letting $t \to \infty$ recovers the Poisson steady state (2.57) of the M/M/∞ queue.
--
--   **Formalization Note** The generating-function identity alone would be a Taylor expansion; the statement ties the Poisson law to the system (2.76) it solves, and adds the uniqueness half in the class of probability solutions.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.101, Eqs. (2.76)–(2.77) and the expansion of (2.77), §2.11.3

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_forwardEquations
import Definitions.Def_QueueingFundamentals_Transient_mmInfTransient

namespace QueueingFundamentals.Transient

/-- (2.77) and the M/M/∞ transient law (p.101). For `λ, μ > 0` and `N(0) = 0`:
the functions `p_n(t) = (1/n!) ((1 - e^{-μt}) λ/μ)^n exp(-(1 - e^{-μt}) λ/μ)` solve the forward
equations (2.76) on `[0, ∞)`, satisfy `p_n(0) = [n = 0]`, form a probability distribution for
every `t ≥ 0`, have generating function
`P(z, t) = ∑ p_n(t) zⁿ = exp((z - 1)(1 - e^{-μt}) λ/μ)` for `|z| ≤ 1`, and are the only
probability solution of (2.76) with that initial condition. -/
theorem mmInf_transient (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) :
    IsForwardSolution (mmInfRHS lam mu) (mmInfTransient lam mu) ∧
      (∀ n : ℕ, mmInfTransient lam mu n 0 = if n = 0 then 1 else 0) ∧
      IsProbabilityFamily (mmInfTransient lam mu) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ z : ℂ, ‖z‖ ≤ 1 →
        HasSum (fun n : ℕ => (mmInfTransient lam mu n t : ℂ) * z ^ n)
          (Complex.exp ((z - 1) * ((1 - Real.exp (-mu * t)) * (lam / mu) : ℝ)))) ∧
      ∀ q : ℕ → ℝ → ℝ, IsForwardSolution (mmInfRHS lam mu) q → IsProbabilityFamily q →
        (∀ n : ℕ, q n 0 = if n = 0 then 1 else 0) →
        ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → q n t = mmInfTransient lam mu n t := by sorry

end QueueingFundamentals.Transient
