-- Prove2me | Theorems.Thm_SAARate_SharpLD_cgf_deriv_abs_le
-- name    : SAARate.SharpLD.cgf_deriv_abs_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:07:34.352982+00:00
-- url     : https://prove2.me/theorems/36297303-2695-4a0d-a6ed-c6ca1c893b13
-- title:
--   Proof of Theorem 3.1, p. 11 — |Λ′(t)| ≤ κ for |X| ≤ κ
-- statement:
--   Let $X$ be a real random variable on a probability space $(\Omega,\mathcal F,P)$ with $|X|\le\kappa$ almost surely. Let $\Lambda(t)=\log\mathbb E[e^{tX}]$ be its logarithmic moment generating function (cumulant generating function). Then $\Lambda$ is differentiable on $\mathbb R$ and, for every $t\in\mathbb R$,
--   $$\Lambda'(t)=\frac{\mathbb E[Xe^{tX}]}{\mathbb E[e^{tX}]},\qquad |\Lambda'(t)|\le\kappa .$$
--
--   In the paper $X=\eta(d,\omega)=h'_\omega(\bar x,d)$ for a fixed direction $d\in T_\Theta(\bar x)\cap S^{m-1}$, and $|X|\le\kappa$ is Assumption (B). The bound is the first step towards the strong convexity of the rate function $I_d=\Lambda^*$.
--
--   **Formalization Note** $\Lambda$ is Mathlib's real-valued `cgf`, which is the true $\log\mathbb E e^{tX}$ here because every exponential moment of a bounded variable is finite. The statement is made for an arbitrary bounded measurable $X$ rather than for $\eta(d,\cdot)$, which makes it more general. The differentiability conjunct makes explicit that `deriv` is the true derivative.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 11, proof of Theorem 3.1, the display |Λ′(t)| ≤ E[|X|e^{tX}]/E[e^{tX}] ≤ κ

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace SAARate.SharpLD

theorem cgf_deriv_abs_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (κ : ℝ)
    (hXκ : ∀ᵐ ω ∂P, |X ω| ≤ κ) :
    Differentiable ℝ (cgf X P) ∧
      ∀ t : ℝ, deriv (cgf X P) t = (∫ ω, X ω * Real.exp (t * X ω) ∂P) / mgf X P t ∧
        |deriv (cgf X P) t| ≤ κ := by sorry

end SAARate.SharpLD
