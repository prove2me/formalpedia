-- Prove2me | Theorems.Thm_QueueingFundamentals_GM1_beta_eq_lst
-- name    : QueueingFundamentals.GM1.beta_eq_lst
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:02:58.115728+00:00
-- url     : https://prove2.me/theorems/583d6917-3c50-4d38-beff-5022d5328147
-- title:
--   Eq. (5.56) — $\beta(z) = A^*[\mu(1-z)]$
-- statement:
--   Consider the G/M/1 queue with interarrival law $A$ on $[0,\infty)$ of mean $1/\lambda$ ($\lambda>0$) and exponential service at rate $\mu > 0$. Let $b_n$ be as in (5.50) and let $A^*(s) = \int_0^\infty e^{-sx}\,dA(x)$ be the Laplace–Stieltjes transform of the interarrival-time CDF. For every complex $z$ with $|z| \le 1$, the series $\beta(z) = \sum_n b_n z^n$ converges and
--   $$
--   \beta(z) = A^*[\mu(1 - z)],
--   $$
--   so that the characteristic equation (5.55) may be written $z = A^*[\mu(1-z)]$ (5.56).
--
--   This is the form in which the root $r_0$ is computed in practice (Example 5.9).
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.261, Eq. (5.56)

import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- Eq. (5.56): for `|z| ≤ 1`, the series `β(z) = ∑ b_n z^n` converges to `A*[μ(1 - z)]`. -/
theorem beta_eq_lst (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => (serviceProb A mu n : ℂ) * z ^ n) (lst A ((mu : ℂ) * (1 - z))) := by sorry

end QueueingFundamentals.GM1
