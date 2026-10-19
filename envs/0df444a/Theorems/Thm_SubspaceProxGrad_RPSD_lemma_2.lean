-- Prove2me | Theorems.Thm_SubspaceProxGrad_RPSD_lemma_2
-- name    : SubspaceProxGrad.RPSD.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:04.467907+00:00
-- url     : https://prove2.me/theorems/cd543365-a054-4a65-b226-ef6603607f7f
-- title:
--   Lemma 2, p. 5 — 𝔼[‖z^k − z⋆‖² | 𝓕^{k−1}] = ‖z^{k−1} − z⋆‖² + ‖y^k − y⋆‖²_P − ‖z^{k−1} − z⋆‖²_P
-- statement:
--   Consider problem (1), $\min_x f(x)+g(x)$, with $f$ differentiable, $\mu$-strongly convex and with $L$-Lipschitz gradient, and $g:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ proper, convex and lower semicontinuous, and let $x^\star$ be its minimizer. Let $\mathfrak S^1,\mathfrak S^2,\dots$ be i.i.d. admissible random subspaces with average projection $\mathsf P=\mathbb E[P_{\mathfrak S^1}]$, let $\mathsf Q=\mathsf P^{-1/2}$, let $\gamma>0$, and let $(x^k),(y^k),(z^k)$ be an RPSD run (Algorithm 1) started at $z^0$. Define the fixed points
--   $$z^\star=y^\star=\mathsf Q\big(x^\star-\gamma\nabla f(x^\star)\big),$$
--   and the filtration $\mathcal F^{k}=\sigma(\mathfrak S^1,\dots,\mathfrak S^{k})$ (so $\mathcal F^0$ is trivial). Then for every $k\ge1$, almost surely,
--   $$\mathbb E\Big[\|z^k-z^\star\|_2^2\,\Big|\,\mathcal F^{k-1}\Big]=\|z^{k-1}-z^\star\|_2^2+\|y^k-y^\star\|_{\mathsf P}^2-\|z^{k-1}-z^\star\|_{\mathsf P}^2 .$$
--
--   This identity writes the one-step change of the distance of $z^k$ to its fixed point as a martingale-type decrease; combined with the contraction of Lemma 3 it yields the expected linear rate of Theorem 1.
--
--   **Formalization Note.** The Lean statement is indexed from the paper's step $k+1$: it conditions $\|z^{k+1}-z^\star\|^2$ on $\sigma(\xi_0,\dots,\xi_{k-1})$, where $\xi_j$ draws $\mathfrak S^{j+1}=\mathrm{sel}(\xi_j)$; for $k=0$ this σ-algebra is trivial and the conditional expectation is the plain expectation. The page names only Assumption 2; Assumption 1 is kept because "the minimizer $x^\star$" is defined through it and because it makes the prox single-valued, so the iterates are determined by the past selections. The step-size bound $\gamma\le2/(\mu+L)$ is not needed and is not assumed; $\gamma>0$ is kept (the prox weight is $1/\gamma$). Added for Lean: $\mu>0$, $L>0$, "$L$-smooth" read as $L$-Lipschitz gradient, measurability of the selection map and of the draws $\xi_k$, and $\mathsf Q=\mathsf P^{-1/2}$ encoded as a positive map with $\mathsf Q\mathsf P\mathsf Q=I$ and a two-sided inverse $\mathsf Q^{-1}$ (this determines $\mathsf Q$ uniquely). The minimizer is quantified universally (it exists and is unique), and so is the run.
-- source:
--   Grishchenko, Iutzeler & Malick, Proximal gradient methods with adaptive subspace sampling, arXiv:2004.13356v1, p. 5, Lemma 2

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic
import Definitions.Def_SubspaceProxGrad_RPSD_Setting

open MeasureTheory ProbabilityTheory

namespace SubspaceProxGrad.RPSD

theorem lemma_2 {n : ℕ} {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
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
    (z0 : E n) (z x : ℕ → Ω → E n) (hrun : IsRPSDRun sel ξ C f g γ Q Qinv z0 z x)
    (k : ℕ) :
    condExp (⨆ j < k, MeasurableSpace.comap (ξ j) ‹MeasurableSpace Θ›) pr
        (fun ω => ‖z (k + 1) ω - Q (xs - γ • gradient f xs)‖ ^ 2)
      =ᵐ[pr] fun ω => ‖z k ω - Q (xs - γ • gradient f xs)‖ ^ 2
        + pNormSq P (Q (x (k + 1) ω - γ • gradient f (x (k + 1) ω)) - Q (xs - γ • gradient f xs))
        - pNormSq P (z k ω - Q (xs - γ • gradient f xs)) := by sorry

end SubspaceProxGrad.RPSD
