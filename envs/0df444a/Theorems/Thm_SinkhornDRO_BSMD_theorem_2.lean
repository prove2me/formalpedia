-- Prove2me | Theorems.Thm_SinkhornDRO_BSMD_theorem_2
-- name    : SinkhornDRO.BSMD.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:27:14.286665+00:00
-- url     : https://prove2.me/theorems/e703ba3e-f32e-4b5c-bf97-7f14e15b4858
-- title:
--   Theorem 2 — BSMD with SG or RT-MLMC subgradients finds a δ-optimal solution of (12), with the explicit hyper-parameters of p. ec20
-- statement:
--   **Setting.** $\Theta\subseteq\mathbb R^{d_\theta}$ is closed and convex. $\|\cdot\|$ is a norm with Assumption EC.1, $\mathfrak c\|\cdot\|_2\le\|\cdot\|\le\mathfrak d\|\cdot\|_2$ with $\mathfrak c>0$. $\omega$ is a distance generating function on $\Theta$, $\kappa$-strongly convex with respect to $\|\cdot\|$, with Bregman divergence $D_\omega$ and prox-mapping $\mathrm{Prox}$ (measurable). $\widehat{\mathbb P}$ is a probability measure and $\mathbb Q$ a Markov kernel on $\mathcal Z$. $\lambda,\epsilon>0$ are fixed. The loss $f_\theta(z)$ is measurable in $z$ and satisfies Assumption 2 with constants $L_f$ and $B$, and $(\theta,z)\mapsto\nabla_\theta f_\theta(z)$ is a jointly measurable subgradient selector. $F$ is the objective (11) and $F^\ell$ its approximation (14).
--
--   **Parameters.** Let $\delta>0$ and $\theta_0\in\Theta$, and put
--   $$K=\frac{B}{\lambda\epsilon},\qquad L=\max\Big(1,\Big\lceil\frac{1}{\log2}\log\frac{2\lambda\epsilon e^{2K}}{\delta}\Big\rceil\Big).$$
--   Let $\theta^*\in\arg\min_\Theta F$ and $\bar\theta^*\in\arg\min_\Theta F^L$, and $D=D_\omega(\theta_0,\bar\theta^*)$. Run BSMD (Algorithm 1) from $\theta_0$ with a fresh independent sample at every iteration, and let $\hat\theta=\frac1T\sum_{t=0}^{T-1}\theta_t$.
--
--   **Claim.** $\hat\theta$ is a $\delta$-optimal solution of (12), $\mathbb E[F(\hat\theta)]-F(\theta^*)\le\delta$, in both of the following cases (and $F(\hat\theta)$ is integrable):
--
--   1. **SG estimator (15)**, with
--   $$T=\max\Big(1,\Big\lceil\frac{8L_f^2D}{\kappa\mathfrak c^2\delta^2}\Big\rceil\Big),\qquad h=\sqrt{\frac{2\kappa\mathfrak c^2D}{TL_f^2}};$$
--   2. **RT-MLMC estimator (17)**, with $M^2=2(L+1)L_f^2e^{4K}/\mathfrak c^2$ and
--   $$T=\max\Big(1,\Big\lceil\frac{16(L+1)L_f^2De^{4K}}{\kappa\mathfrak c^2\delta^2}\Big\rceil\Big),\qquad h=\sqrt{\frac{2\kappa D}{TM^2}} .$$
--
--   The paper states the result as sample complexities: (I) $O(\delta^{-2})$ samples from $\widehat{\mathbb P}$ and $O(\lambda\epsilon e^{2K}\delta^{-3})$ from $\mathbb Q_{x,\epsilon}$ for SG; (II) $\tilde O(Ke^{4K}\delta^{-2})$ and $\tilde O(K^2e^{4K}\delta^{-2})$ for RT-MLMC. Its proof yields the hyper-parameters above. The counts follow by construction: one sample from $\widehat{\mathbb P}$ per iteration, and $2^L$ draws from $\mathbb Q_x$ per SG iteration or $(L+1)/(2-2^{-L})$ per RT-MLMC iteration in expectation.
--
--   **Formalization Note** The paper writes $O(\cdot)$ and $\tilde O(\cdot)$; its proof (p. ec20) yields the explicit $L,T,h$ above, which are fixed here rather than existentially quantified. The `max 1` guards keep $L\in\mathbb N_+$ and $T\ge1$. Two corrections are made, both recorded in the items they come from. First, $\hat\theta$ averages $\theta_0,\dots,\theta_{T-1}$ instead of the printed $\theta_1,\dots,\theta_T$ (see Lemma EC.7). Second, $M^2$ carries $\mathfrak c^{-2}$ (see the RT-MLMC second-moment item). $\mathbb Q$ is any Markov kernel, which includes the paper's Gibbs kernel $\mathbb Q_{x,\epsilon}$. The per-iteration sampling laws are probability measures; they are supplied as instance arguments because Lean's finite product measure needs them. Measurability of $\mathrm{Prox}$ and of the subgradient selector is the standing convention that makes $\mathbb E[F(\hat\theta)]$ meaningful.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. 18, Theorem 2; explicit hyper-parameters from App. EC.6.1, p. ec20

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_MirrorSetup
import Definitions.Def_SinkhornDRO_BSMD_Objective
import Definitions.Def_SinkhornDRO_BSMD_Estimators

open MeasureTheory ProbabilityTheory

namespace SinkhornDRO.BSMD

/-- Theorem 2 (Wang–Gao–Xie, arXiv:2109.11926v5, p. 18), in the explicit form of its proof
(App. EC.6.1, p. ec20). Fix `λ, ε, δ > 0`, put `K = B/(λε)`,
`L = max 1 ⌈log(2λε e^{2K}/δ) / log 2⌉`, let `θ̄*` minimize `F^L` and `θ*` minimize `F` over `Θ`,
and `D = D_ω(θ0, θ̄*)`. Under Assumption 2, BSMD (Algorithm 1) from `θ0 ∈ Θ` returns a δ-optimal
solution, `E[F(θ̂)] − F(θ*) ≤ δ`:
(I) with the SG estimator (15), `T = max 1 ⌈8 L_f² D/(κ𝔠²δ²)⌉` and `h = √(2κ𝔠²D/(T L_f²))`;
(II) with the RT-MLMC estimator (17), `T = max 1 ⌈16(L+1) L_f² D e^{4K}/(κ𝔠²δ²)⌉` and
`h = √(2κD/(T M²))`, `M² = 2(L+1) L_f² e^{4K}/𝔠²`.
Each iteration draws a fresh, independent sample; `θ̂` averages the query points
`θ_0, …, θ_{T−1}`. -/
theorem theorem_2 {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (Θ : Set (Param d)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (𝒩 : MirrorNorm d) (κ : ℝ) (ω : Param d → ℝ) (ω' : Param d → Param d)
    (hω : IsDistGen Θ 𝒩 κ ω ω')
    (prox : Param d → Param d → Param d) (hprox : IsProxMap Θ ω ω' prox)
    (hprox_meas : Measurable (Function.uncurry prox))
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (lam eps : ℝ) (hlam : 0 < lam) (heps : 0 < eps)
    (f : Param d → Z → ℝ) (hf_meas : ∀ θ, Measurable (f θ))
    (Lf B : ℝ) (hA2I : Asm2Convex f) (hA2II : Asm2Lipschitz f Lf) (hA2III : Asm2Bounded Θ f B)
    (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg)
    (hsg_meas : Measurable (Function.uncurry sg))
    (δ : ℝ) (hδ : 0 < δ)
    (θ0 : Param d) (hθ0 : θ0 ∈ Θ)
    (θstar : Param d)
    (hθstar : θstar ∈ Θ ∧ ∀ θ ∈ Θ, objF P Q lam eps f θstar ≤ objF P Q lam eps f θ)
    (θbar : Param d)
    (hθbar : θbar ∈ Θ ∧ ∀ θ ∈ Θ,
      objFℓ P Q lam eps f (levelL lam eps B δ) θbar ≤ objFℓ P Q lam eps f (levelL lam eps B δ) θ)
    [IsProbabilityMeasure (levelLaw P Q (2 ^ levelL lam eps B δ))]
    [IsProbabilityMeasure (rtLaw P Q (levelL lam eps B δ))] :
    let K := B / (lam * eps)
    let L := levelL lam eps B δ
    let D := bregman ω ω' θ0 θbar
    -- (I) SG estimator
    (let T := iterSG Lf κ 𝒩.c D δ
     let h := stepSG Lf κ 𝒩.c D T
     Integrable (fun ξ : Fin T → Z × (Fin (2 ^ L) → Z) =>
         objF P Q lam eps f (bsmdAvg prox (vSG lam eps f sg L) h θ0 ξ))
         (Measure.pi fun _ => levelLaw P Q (2 ^ L)) ∧
       ∫ ξ, objF P Q lam eps f (bsmdAvg prox (vSG lam eps f sg L) h θ0 ξ)
           ∂(Measure.pi fun _ : Fin T => levelLaw P Q (2 ^ L))
         - objF P Q lam eps f θstar ≤ δ) ∧
    -- (II) RT-MLMC estimator
    (let T := iterRT L Lf K κ 𝒩.c D δ
     let h := stepRT L Lf K κ 𝒩.c D T
     Integrable (fun ξ : Fin T → Fin (L + 1) × Z × (Fin (2 ^ L) → Z) =>
         objF P Q lam eps f (bsmdAvg prox (vRT lam eps f sg L) h θ0 ξ))
         (Measure.pi fun _ => rtLaw P Q L) ∧
       ∫ ξ, objF P Q lam eps f (bsmdAvg prox (vRT lam eps f sg L) h θ0 ξ)
           ∂(Measure.pi fun _ : Fin T => rtLaw P Q L)
         - objF P Q lam eps f θstar ≤ δ) := by sorry

end SinkhornDRO.BSMD
