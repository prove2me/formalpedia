-- Prove2me | Theorems.Thm_SubspaceProxGrad_RPSD_thm1_display_a
-- name    : SubspaceProxGrad.RPSD.thm1_display_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:01.049629+00:00
-- url     : https://prove2.me/theorems/9f529b5e-704d-4250-8240-2c91389fbf4d
-- title:
--   Proof of Theorem 1, p. 6, display (a) — 𝔼‖z^k − z⋆‖² ≤ (1 − λmin(P)·2γμL/(μ+L))^k ‖z⁰ − z⋆‖²
-- statement:
--   Under the assumptions of Theorem 1 — $f$ differentiable, $\mu$-strongly convex with $L$-Lipschitz gradient, $g$ proper convex lower semicontinuous, $x^\star$ the minimizer of $f+g$, i.i.d. admissible selections with average projection $\mathsf P$, $\mathsf Q=\mathsf P^{-1/2}$, and $\gamma\in(0,2/(\mu+L)]$ — every RPSD run started at $z^0$ satisfies, for every $k\ge0$,
--   $$\mathbb E\big[\|z^k-z^\star\|_2^2\big]\le\Big(1-\lambda_{\min}(\mathsf P)\frac{2\gamma\mu L}{\mu+L}\Big)^k\|z^0-z^\star\|_2^2,\qquad z^\star=\mathsf Q\big(x^\star-\gamma\nabla f(x^\star)\big).$$
--
--   This is the linear convergence in expectation of the auxiliary sequence $(z^k)$, the step of the proof of Theorem 1 that follows from Lemmas 2 and 3 by taking full expectations along the nested filtrations; the rate for the iterates $x^k$ then follows from display (b).
--
--   **Formalization Note.** The expectation is a Bochner integral over the probability space. The conventions are those of Theorem 1: $\mathfrak S^{k+1}=\mathrm{sel}(\xi_k)$, $\mathsf Q$ positive with $\mathsf Q\mathsf P\mathsf Q=I$ and a two-sided inverse, $\mu,L>0$, $L$-Lipschitz gradient, measurable selections, and universally quantified minimizer and run.
-- source:
--   Grishchenko, Iutzeler & Malick, Proximal gradient methods with adaptive subspace sampling, arXiv:2004.13356v1, p. 6, proof of Theorem 1, display (a) (after "and thus by taking the full expectation")

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic
import Definitions.Def_SubspaceProxGrad_RPSD_Setting

open MeasureTheory ProbabilityTheory

namespace SubspaceProxGrad.RPSD

theorem thm1_display_a {n : ℕ} {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (pr : Measure Ω) [IsProbabilityMeasure pr]
    (sel : Θ → Submodule ℝ (E n)) (hsel : ∀ x : E n, Measurable fun θ => (sel θ).starProjection x)
    (ξ : ℕ → Ω → Θ) (hξ : ∀ k, Measurable (ξ k)) (hind : iIndepFun ξ pr)
    (hid : ∀ k, IdentDistrib (ξ k) (ξ 0) pr pr)
    (hadm : IsAdmissible pr (fun ω => sel (ξ 0 ω)))
    (P : E n →L[ℝ] E n) (hP : IsAvgProj pr (fun ω => sel (ξ 0 ω)) P)
    (Q Qinv : E n →L[ℝ] E n) (hQ : Q.IsPositive)
    (hQPQ : Q ∘L P ∘L Q = ContinuousLinearMap.id ℝ (E n))
    (hQi : Q ∘L Qinv = ContinuousLinearMap.id ℝ (E n))
    (hQi' : Qinv ∘L Q = ContinuousLinearMap.id ℝ (E n))
    (f : E n → ℝ) (μ L : ℝ) (hμ : 0 < μ) (hL : 0 < L) (hfd : Differentiable ℝ f)
    (hfs : StrongConvexOn Set.univ μ f)
    (hfL : ∀ x y : E n, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (C : Set (E n)) (g : E n → ℝ) (hC : C.Nonempty) (hg : ConvexOn ℝ C g)
    (hgl : IsClosed {p : E n × ℝ | p.1 ∈ C ∧ g p.1 ≤ p.2})
    (xs : E n) (hxs : IsMinimizer C f g xs)
    (γ : ℝ) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 2 / (μ + L))
    (z0 : E n) (z x : ℕ → Ω → E n) (hrun : IsRPSDRun sel ξ C f g γ Q Qinv z0 z x) :
    ∀ k : ℕ, ∫ ω, ‖z k ω - Q (xs - γ • gradient f xs)‖ ^ 2 ∂pr ≤
      (1 - lamMin P * (2 * γ * μ * L / (μ + L))) ^ k * ‖z0 - Q (xs - γ • gradient f xs)‖ ^ 2 := by sorry

end SubspaceProxGrad.RPSD
