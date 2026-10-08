-- Prove2me | Theorems.Thm_QueueingFundamentals_GG1_mdc_pgf
-- name    : QueueingFundamentals.GG1.mdc_pgf
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T19:49:01.719873+00:00
-- url     : https://prove2.me/theorems/15f5b90e-ad51-4469-ac66-e810df7d873b
-- title:
--   Eq. (6.18) — the M/D/c generating function
-- statement:
--   Consider the M/D/c queue with $c\ge1$ servers, the constant service time as the unit of time, and Poisson arrivals at rate $\lambda>0$ per unit. If $\lambda<c$, a steady-state distribution $(p_n)$ solving (6.17) exists. For every steady-state distribution, with $P_c=\sum_{n=0}^{c}p_n$ and $P(z)=\sum_{n\ge0}p_nz^n$, and every complex $z$ with $|z|\le1$,
--
--   $$
--   P(z)=\frac{\sum_{n=0}^{c}p_nz^n-P_cz^c}{1-z^ce^{\lambda(1-z)}}=\frac{\sum_{n=0}^{c-1}p_n(z^n-z^c)}{1-z^ce^{\lambda(1-z)}}. \tag{6.18}
--   $$
--
--   This expresses the queue-size generating function through the $c$ unknown probabilities $p_0,\dots,p_{c-1}$, which the roots of the denominator then determine.
--
--   **Formalization Note** (6.18) is stated with its denominator cleared, $P(z)\bigl(1-z^ce^{\lambda(1-z)}\bigr)=\dots$, on the whole closed disk; this is equivalent to the quotient wherever the denominator is nonzero and additionally says that the numerator vanishes at the zeros of the denominator. The existence half under $\lambda<c$ is the book's steady-state assumption ($\rho=\lambda/c<1$ after rescaling time).
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.295, Eq. (6.18), from Eq. (6.17)

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_MDc

namespace QueueingFundamentals.GG1

/-- Eq. (6.18) (p.295) for the M/D/c queue (`c` servers, constant service time taken as the unit of
time, Poisson arrivals at rate `λ > 0` per unit). Under the steady-state condition `λ < c` a
probability solution of (6.17) exists; and for every probability solution `p` of (6.17) and every
`|z| ≤ 1`,
`P(z)(1 − z^c e^{λ(1−z)}) = ∑_{n=0}^{c} p_n z^n − P_c z^c = ∑_{n=0}^{c−1} p_n (z^n − z^c)`,
the cleared-denominator form of `P(z) = (∑_{n=0}^{c} p_n z^n − P_c z^c)/(1 − z^c e^{λ(1−z)})`. -/
theorem mdc_pgf (lam : ℝ) (hlam : 0 < lam) (c : ℕ) (hc : 1 ≤ c) :
    ((lam < c) → ∃ p : ℕ → ℝ, IsMDcStationary lam c p) ∧
    ∀ p : ℕ → ℝ, IsMDcStationary lam c p → ∀ z : ℂ, ‖z‖ ≤ 1 →
      QueueingFundamentals.MG1.pgf p z * (1 - z ^ c * Complex.exp ((lam : ℂ) * (1 - z))) =
          (∑ n ∈ Finset.range (c + 1), (p n : ℂ) * z ^ n) - (cumProb p c : ℂ) * z ^ c ∧
      QueueingFundamentals.MG1.pgf p z * (1 - z ^ c * Complex.exp ((lam : ℂ) * (1 - z))) =
          ∑ n ∈ Finset.range c, (p n : ℂ) * (z ^ n - z ^ c) := by sorry

end QueueingFundamentals.GG1
