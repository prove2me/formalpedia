-- Prove2me | Theorems.Thm_ShockWear_Inherit_theorem31_2
-- name    : ShockWear.Inherit.theorem31_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:06.235626+00:00
-- url     : https://prove2.me/theorems/4bd02ac1-731c-40e1-a06d-73e53d7c2350
-- title:
--   Theorem 3.1(3.2) — PF₂ shock survival gives increasing hazard rate
-- statement:
--   Let shocks arrive at rate $\lambda>0$, and let $1=\bar P_0\geq\bar P_1\geq\cdots\geq0$ be the probabilities of surviving the first $k$ shocks. Suppose the successive ratios $\theta_k=\bar P_k/\bar P_{k-1}$ decrease weakly for $k\geq1$, equivalently that $(\bar P_k)_{k\geq0}$ is PF₂. Then the survival function
--
--   $$\bar H(t)=\sum_{k\geq0}\bar P_k e^{-\lambda t}(\lambda t)^k/k!,\qquad t\geq0,$$
--
--   has increasing hazard rate: for every $x>0$ and $s\leq t$,
--
--   $$\bar H(x+t)\bar H(s)\leq\bar H(x+s)\bar H(t).$$
--
--   Thus a discrete reliability property of the shock sequence passes to the continuous lifetime law under Poisson arrivals.
--
--   **Formalization Note** The successive-ratio condition and IHR conclusion are cross-multiplied to cover zero survival probabilities. For negative times, $\bar H=1$ as in (2.1), and the IHR relation is stated on the full real line; $\bar P_0=1$ avoids an atom at zero.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 632, Theorem 3.1(3.2); https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit

/-- Theorem 3.1(3.2): discrete PF₂ shock survival gives an IHR life law. -/
theorem theorem31_2 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 = 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hpf : IsPF2SeqFrom 0 P) :
    IsIHR (ShockWear.CumDamage.shockSurv lam P) := by sorry

end ShockWear.Inherit
