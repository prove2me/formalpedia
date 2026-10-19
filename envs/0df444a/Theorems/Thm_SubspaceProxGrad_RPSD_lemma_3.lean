-- Prove2me | Theorems.Thm_SubspaceProxGrad_RPSD_lemma_3
-- name    : SubspaceProxGrad.RPSD.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:12.763651+00:00
-- url     : https://prove2.me/theorems/ea26ab92-5199-4fe1-b451-a1f7ec2d2c62
-- title:
--   Lemma 3, p. 6 — ‖y^k − y⋆‖²_P − ‖z^{k−1} − z⋆‖²_P ≤ −λmin(P)·(2γμL/(μ+L))·‖z^{k−1} − z⋆‖² (with γ ∈ (0, 2/(μ+L)])
-- statement:
--   Consider problem (1), $\min_x f(x)+g(x)$, with $f$ differentiable, $\mu$-strongly convex and with $L$-Lipschitz gradient ($0<\mu$, $0<L$), and $g:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ proper, convex and lower semicontinuous, and let $x^\star$ be its minimizer. Let $\mathfrak S^1,\mathfrak S^2,\dots$ be i.i.d. admissible random subspaces with average projection $\mathsf P$, let $\mathsf Q=\mathsf P^{-1/2}$, and let the step size satisfy
--   $$0<\gamma\le\frac{2}{\mu+L}.$$
--   Put $z^\star=y^\star=\mathsf Q(x^\star-\gamma\nabla f(x^\star))$. For any point $z^{k-1}\in\mathbb R^n$, let $x^k=\mathbf{prox}_{\gamma g}(\mathsf Q^{-1}z^{k-1})$ and $y^k=\mathsf Q(x^k-\gamma\nabla f(x^k))$. Then
--   $$\|y^k-y^\star\|_{\mathsf P}^2-\|z^{k-1}-z^\star\|_{\mathsf P}^2\le-\lambda_{\min}(\mathsf P)\,\frac{2\gamma\mu L}{\mu+L}\,\|z^{k-1}-z^\star\|_2^2 .$$
--
--   This is the deterministic contraction step of the analysis: one forward–backward step, measured in the $\mathsf P$-weighted norm, contracts the distance to the fixed point by a factor depending only on $\mu$, $L$, $\gamma$ and $\lambda_{\min}(\mathsf P)$.
--
--   **Formalization Note.** The step-size range $\gamma\in(0,2/(\mu+L)]$ is added to the hypotheses: the printed lemma omits it, but its proof uses it ("Using the standard stepsize range"), and the inequality is false without it (for $f=\tfrac L2\|x\|^2$, $g=0$ and large $\gamma$). The point $z^{k-1}$ is arbitrary (the lemma is deterministic), and $x^k$ is any point satisfying the prox optimality condition. Assumption 2 (the i.i.d. admissible selections defining $\mathsf P$) is kept as on the page. Added for Lean: $\mu>0$, $L>0$, $L$-Lipschitz gradient for "$L$-smooth", measurability of the selections, and $\mathsf Q$ encoded as a positive map with $\mathsf Q\mathsf P\mathsf Q=I$ and a two-sided inverse.
-- source:
--   Grishchenko, Iutzeler & Malick, Proximal gradient methods with adaptive subspace sampling, arXiv:2004.13356v1, p. 6, Lemma 3 (step-size range from its proof)

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic
import Definitions.Def_SubspaceProxGrad_RPSD_Setting

open MeasureTheory ProbabilityTheory

namespace SubspaceProxGrad.RPSD

theorem lemma_3 {n : ℕ} {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
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
    (w xk : E n) (hxk : BoydADMM.Prox.IsProx C g (1 / γ) (Qinv w) xk) :
    pNormSq P (Q (xk - γ • gradient f xk) - Q (xs - γ • gradient f xs))
        - pNormSq P (w - Q (xs - γ • gradient f xs))
      ≤ -(lamMin P * (2 * γ * μ * L / (μ + L))) * ‖w - Q (xs - γ • gradient f xs)‖ ^ 2 := by sorry

end SubspaceProxGrad.RPSD
