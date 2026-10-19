-- Prove2me | Theorems.Thm_RedundancyStab_IID_lemma_2
-- name    : RedundancyStab.IID.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:44.140353+00:00
-- url     : https://prove2.me/theorems/b32a011c-745f-4469-bac9-eda8b897c4bc
-- title:
--   Lemma 2, p. 7 — at a most-loaded server the fluid number of copies satisfies dm_s/dt ≤ λd/K − µd
-- statement:
--   Consider the redundancy-$d$ model with i.i.d. $\mathrm{Exp}(\mu)$ copies under PS or under ROS, $1\le d\le K$, $\lambda>0$, $\mu>0$, and a fluid initial state $\vec n(0)\in\mathbb R_{\ge0}^C$. For almost every sample point $\omega$ the following holds for every fluid limit $(\vec n,\vec\tau)$ at $\omega$. Write
--   $$m_s(t):=\sum_{c\in C(s)}n_c(t).$$
--   If $t>0$, every $n_c$ is differentiable at $t$, and $m_s(t)=\max_{l\in S}m_l(t)>0$, then
--   $$\frac{dm_s(t)}{dt}\le\frac{\lambda d}{K}-\mu d.$$
--
--   When $\rho=\lambda/(\mu K)<1$ the right-hand side is negative, so the largest fluid queue decreases at a constant rate; this gives the emptying time in the proof of Proposition 3.
--
--   **Formalization Note** Fluid limits are Lipschitz, so derivatives exist only almost everywhere; the inequality is stated at points where every $n_c$ is differentiable, which is where the paper's argument (12) applies (a hypothesis-free `deriv` would be the junk value $0$ elsewhere). For ROS the paper's proof applies the PS rate (1); the ROS case is stated as printed.
-- source:
--   Anton, Ayesta, Jonckheere & Verloop, On the stability of redundancy models, arXiv:1903.04414v2, p. 7, Lemma 2 (proof pp. 26–27)

import Mathlib
import Definitions.Def_RedundancyStab_IID_FluidModel

namespace RedundancyStab.IID

open MeasureTheory ProbabilityTheory Filter

theorem lemma_2 {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (K d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ)
    (P : Primitives K d lam μ Ω) (pol : Policy) (n0 : JobType K d → ℝ) (hn0 : ∀ c, 0 ≤ n0 c) :
    ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ n τ : JobType K d → ℝ → ℝ, IsFluidLimitAt P pol n0 ω n τ →
      ∀ (s : Fin K) (t : ℝ), 0 < t → (∀ c, DifferentiableAt ℝ (n c) t) →
        (∀ l, fluidCopies K d (fun c => n c t) l ≤ fluidCopies K d (fun c => n c t) s) →
        0 < fluidCopies K d (fun c => n c t) s →
        deriv (fun t' => fluidCopies K d (fun c => n c t') s) t ≤ lam * d / K - μ * d := by sorry

end RedundancyStab.IID
