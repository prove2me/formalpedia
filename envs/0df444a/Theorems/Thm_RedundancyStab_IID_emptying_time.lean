-- Prove2me | Theorems.Thm_RedundancyStab_IID_emptying_time
-- name    : RedundancyStab.IID.emptying_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:38.087982+00:00
-- url     : https://prove2.me/theorems/5613284c-38cb-46bc-87f1-5f77ddb81931
-- title:
--   Proof of Proposition 3, p. 27 — if ρ < 1, every fluid limit is empty at T = m_max(0)/(d(µ − λ/K))
-- statement:
--   Consider the redundancy-$d$ model with i.i.d. $\mathrm{Exp}(\mu)$ copies under PS or under ROS, $1\le d\le K$, $\lambda>0$, $\mu>0$, and assume
--   $$\rho=\frac{\lambda}{\mu K}<1 .$$
--   Fix a fluid initial state $\vec n(0)\in\mathbb R_{\ge0}^C$. For almost every sample point $\omega$, every fluid limit $(\vec n,\vec\tau)$ at $\omega$ satisfies $n_c(T)=0$ for all $c\in C$, where
--   $$T=\frac{m_{\max}(0)}{d\,(\mu-\lambda/K)},\qquad m_{\max}(0)=\max_{s\in S}\sum_{c\in C(s)}n_c(0).$$
--
--   An empty fluid model at a fixed time is the hypothesis of the fluid-stability theorem (Robert 2003, Corollary 9.8) from which the paper concludes Proposition 3.
--
--   **Formalization Note** $m_{\max}(0)$ is the maximum over the (nonempty, since $K\ge d\ge1$) finite set of servers, written as `⨆ s : Fin K`; it is computed from the fluid limit's own value $n_c(0)$.
-- source:
--   Anton, Ayesta, Jonckheere & Verloop, On the stability of redundancy models, arXiv:1903.04414v2, p. 27, proof of Proposition 3

import Mathlib
import Definitions.Def_RedundancyStab_IID_FluidModel

namespace RedundancyStab.IID

open MeasureTheory ProbabilityTheory Filter

theorem emptying_time {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (K d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ)
    (hρ : lam / (μ * K) < 1)
    (P : Primitives K d lam μ Ω) (pol : Policy) (n0 : JobType K d → ℝ) (hn0 : ∀ c, 0 ≤ n0 c) :
    ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ n τ : JobType K d → ℝ → ℝ, IsFluidLimitAt P pol n0 ω n τ →
      ∀ c, n c ((⨆ s : Fin K, fluidCopies K d (fun c' => n c' 0) s) /
        ((d : ℝ) * (μ - lam / K))) = 0 := by sorry

end RedundancyStab.IID
