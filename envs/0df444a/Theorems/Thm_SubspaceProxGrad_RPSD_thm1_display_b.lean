-- Prove2me | Theorems.Thm_SubspaceProxGrad_RPSD_thm1_display_b
-- name    : SubspaceProxGrad.RPSD.thm1_display_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:58.786665+00:00
-- url     : https://prove2.me/theorems/0459e61f-149c-4fe1-a5e4-c7b76b619c9b
-- title:
--   Proof of Theorem 1, p. 6, display (b) — ‖x^{k+1} − x⋆‖² ≤ ‖z^k − z⋆‖²_P ≤ λmax(P)‖z^k − z⋆‖²
-- statement:
--   Under the assumptions of Theorem 1 (with any step size $\gamma>0$), every RPSD run satisfies, for every $k\ge0$ and every outcome,
--   $$\|x^{k+1}-x^\star\|_2^2\le\|z^k-z^\star\|_{\mathsf P}^2\le\lambda_{\max}(\mathsf P)\,\|z^k-z^\star\|_2^2,\qquad z^\star=\mathsf Q\big(x^\star-\gamma\nabla f(x^\star)\big).$$
--
--   It transfers bounds on the auxiliary sequence $(z^k)$ to the iterates $x^{k+1}=\mathbf{prox}_{\gamma g}(\mathsf Q^{-1}z^k)$, and is the step that turns display (a) into the rate of Theorem 1, with the constant $\lambda_{\max}(\mathsf P)$.
--
--   **Formalization Note.** The inequality holds pathwise, for every outcome. The step-size bound $\gamma\le2/(\mu+L)$ is not needed and is not assumed ($\gamma>0$ is kept); the remaining hypotheses are those of Theorem 1, with the same conventions ($\mathfrak S^{k+1}=\mathrm{sel}(\xi_k)$, $\mathsf Q$ positive with $\mathsf Q\mathsf P\mathsf Q=I$ and a two-sided inverse, $\mu,L>0$, $L$-Lipschitz gradient).
-- source:
--   Grishchenko, Iutzeler & Malick, Proximal gradient methods with adaptive subspace sampling, arXiv:2004.13356v1, p. 6, proof of Theorem 1, display (b) (after "Using the same arguments as in the proof of Lemma 3")

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic
import Definitions.Def_SubspaceProxGrad_RPSD_Setting

open MeasureTheory ProbabilityTheory

namespace SubspaceProxGrad.RPSD

theorem thm1_display_b {n : ℕ} {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
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
    (z0 : E n) (z x : ℕ → Ω → E n) (hrun : IsRPSDRun sel ξ C f g γ Q Qinv z0 z x) :
    ∀ (k : ℕ) (ω : Ω),
      ‖x (k + 1) ω - xs‖ ^ 2 ≤ pNormSq P (z k ω - Q (xs - γ • gradient f xs)) ∧
        pNormSq P (z k ω - Q (xs - γ • gradient f xs)) ≤ lamMax P * ‖z k ω - Q (xs - γ • gradient f xs)‖ ^ 2 := by sorry

end SubspaceProxGrad.RPSD
