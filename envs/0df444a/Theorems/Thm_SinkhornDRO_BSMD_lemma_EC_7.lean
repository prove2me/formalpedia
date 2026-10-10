-- Prove2me | Theorems.Thm_SinkhornDRO_BSMD_lemma_EC_7
-- name    : SinkhornDRO.BSMD.lemma_EC_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:20.226561+00:00
-- url     : https://prove2.me/theorems/ddd2a439-fd4d-4ed0-854b-337b54b76a18
-- title:
--   Lemma EC.7 — biased stochastic mirror descent: E[F(θ̂) − F(θ*)] ≤ 2Δ_F + M_*√(2D_ω(θ0, θ̄*)/(κT))
-- statement:
--   Let $\Theta\subseteq\mathbb R^{d_\theta}$ be closed and convex, let $\|\cdot\|$ satisfy Assumption EC.1 with dual norm $\|\cdot\|_*$, let $\omega$ be a distance generating function on $\Theta$, $\kappa$-strongly convex with respect to $\|\cdot\|$, with Bregman divergence $D_\omega$ and prox-mapping $\mathrm{Prox}$ (measurable in both arguments).
--
--   Consider $\min_{\theta\in\Theta}F(\theta)$ for a measurable $F$, and an approximation $\bar F$ with
--   $$|\bar F(\theta)-F(\theta)|\le\Delta_F\qquad\forall\theta\in\Theta .$$
--   Let $\nabla\bar F(\theta)$ be a subgradient of $\bar F$ at $\theta$ relative to $\Theta$ for every $\theta\in\Theta$. Let $v(\theta,\xi)$ be a jointly measurable estimator, $\xi\sim\mu$ a sample from a probability measure $\mu$, such that for every $\theta\in\Theta$
--   $$\mathbb E[v(\theta,\xi)]=\nabla\bar F(\theta),\qquad\mathbb E\big[\|v(\theta,\xi)\|_*^2\big]\le M_*^2$$
--   (both integrands integrable), with $M_*>0$. Let $\bar\theta^*\in\arg\min_\Theta\bar F$, $\theta^*\in\arg\min_\Theta F$, $\theta_0\in\Theta$ and $T\ge1$. Run
--   $$\theta_{t+1}=\mathrm{Prox}_{\theta_t}\big(h\,v(\theta_t,\xi_t)\big),\quad t=0,\dots,T-1,\qquad h=\sqrt{\frac{2\kappa D_\omega(\theta_0,\bar\theta^*)}{TM_*^2}},$$
--   with $\xi_0,\dots,\xi_{T-1}$ i.i.d. $\sim\mu$, and let $\hat\theta=\frac1T\sum_{t=0}^{T-1}\theta_t$. Then $F(\hat\theta)$ is integrable and
--   $$\mathbb E\big[F(\hat\theta)-F(\theta^*)\big]\le2\Delta_F+M_*\sqrt{\frac{2D_\omega(\theta_0,\bar\theta^*)}{\kappa T}} .$$
--
--   This is the convergence guarantee of BSMD on which both parts of Theorem 2 rest: the bias of the subgradients enters only additively, through $2\Delta_F$.
--
--   **Formalization Note** The paper defines $\hat\theta=\frac1T\sum_{t=1}^{T}\theta_t$. With that average the lemma is false. Take $\mathbb R^2$ with the Euclidean norm, $\omega=\frac12\|\cdot\|^2$ ($\kappa=1$, $\mathrm{Prox}_\theta(y)=\theta-y$), $\bar F=F$, $\Delta_F=0$, and $F(x)=\max\big(cx_1,\;cx_1+sx_2,\;cx_1-sx_2,\;-x_1\big)$ with $c=\tfrac14$, $s=\sqrt{1-c^2}$. This $F$ is convex and 1-Lipschitz, with unique minimizer $0$. At $\theta_0=(1,0)$ let $v=(c,\pm s)$, each with probability $\tfrac12$, and elsewhere a deterministic subgradient; then $M_*=1$. For $T=1$ we get $h=1$ and $\theta_1=(1-c,\mp s)$, so $F(\theta_1)=c(1-c)+s^2=\tfrac98$, which exceeds the bound $M_*\sqrt{2D/\kappa}=1$. The standard analysis the paper invokes (its reference [77], §2.3, which indexes from $x_1$) bounds the average of the $T$ query points, here $\theta_0,\dots,\theta_{T-1}$. That is the average used here. Measurability of $F$, $v$ and $\mathrm{Prox}$ is the standing convention that makes the expectation meaningful, and the integrability of $F(\hat\theta)$ is part of the conclusion.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. ec19, App. EC.6.1, setup paragraph and Lemma EC.7 (averaging index corrected, see Formalization Note)

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_MirrorSetup

open MeasureTheory
open scoped RealInnerProductSpace

namespace SinkhornDRO.BSMD

/-- Lemma EC.7 (Wang–Gao–Xie, arXiv:2109.11926v5, p. ec19): BSMD for a nonsmooth convex problem
`min_{θ∈Θ} F(θ)` run on subgradient estimates of an approximation `F̄` with bias `Δ_F`, with the
step `h = √(2κ D_ω(θ0, θ̄*) / (T M_*²))`, satisfies
`E[F(θ̂) − F(θ*)] ≤ 2Δ_F + M_* √(2 D_ω(θ0, θ̄*) / (κT))`.
Here `θ̂` is the average of the query points `θ_0, …, θ_{T−1}` (the paper prints `θ_1, …, θ_T`,
for which the inequality fails; see the natural-language statement). The `T` samples are i.i.d.
with law `μ`. -/
theorem lemma_EC_7 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (Θ : Set (Param d)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (𝒩 : MirrorNorm d) (κ : ℝ) (ω : Param d → ℝ) (ω' : Param d → Param d)
    (hω : IsDistGen Θ 𝒩 κ ω ω')
    (prox : Param d → Param d → Param d) (hprox : IsProxMap Θ ω ω' prox)
    (hprox_meas : Measurable (Function.uncurry prox))
    (F Fbar : Param d → ℝ) (hF_meas : Measurable F) (ΔF : ℝ)
    (hbias : ∀ θ ∈ Θ, |Fbar θ - F θ| ≤ ΔF)
    (sgbar : Param d → Param d)
    (hsgbar : ∀ θ ∈ Θ, ∀ θ' ∈ Θ, Fbar θ + ⟪sgbar θ, θ' - θ⟫ ≤ Fbar θ')
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (v : Param d → Ω → Param d) (hv_meas : Measurable (Function.uncurry v))
    (M : ℝ) (hM : 0 < M)
    (hv_int : ∀ θ ∈ Θ, Integrable (v θ) μ)
    (hv_mean : ∀ θ ∈ Θ, ∫ s, v θ s ∂μ = sgbar θ)
    (hv_sq : ∀ θ ∈ Θ, Integrable (fun s => dualNorm 𝒩 (v θ s) ^ 2) μ ∧
      ∫ s, dualNorm 𝒩 (v θ s) ^ 2 ∂μ ≤ M ^ 2)
    (θbar : Param d) (hθbar : θbar ∈ Θ ∧ ∀ θ ∈ Θ, Fbar θbar ≤ Fbar θ)
    (θstar : Param d) (hθstar : θstar ∈ Θ ∧ ∀ θ ∈ Θ, F θstar ≤ F θ)
    (θ0 : Param d) (hθ0 : θ0 ∈ Θ)
    (T : ℕ) (hT : 0 < T) :
    let h := Real.sqrt (2 * κ * bregman ω ω' θ0 θbar / (T * M ^ 2))
    Integrable (fun ξ : Fin T → Ω => F (bsmdAvg prox v h θ0 ξ)) (Measure.pi fun _ => μ) ∧
      ∫ ξ, (F (bsmdAvg prox v h θ0 ξ) - F θstar) ∂(Measure.pi fun _ : Fin T => μ)
        ≤ 2 * ΔF + M * Real.sqrt (2 * bregman ω ω' θ0 θbar / (κ * T)) := by sorry

end SinkhornDRO.BSMD
