-- Prove2me | Theorems.Thm_SinkhornDRO_BSMD_rtmlmc_second_moment
-- name    : SinkhornDRO.BSMD.rtmlmc_second_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:26:34.913252+00:00
-- url     : https://prove2.me/theorems/f8ba74ee-0e6c-47e8-bb33-e8d979358248
-- title:
--   App. EC.6.1, p. ec20 — E‖v^{RT-MLMC}(θ)‖_*² ≤ 2(L+1) L_f² exp(4B/(λε)) / 𝔠²
-- statement:
--   Let $\Theta$ be closed and convex, let $\|\cdot\|$ satisfy Assumption EC.1 with constant $\mathfrak c>0$ and dual norm $\|\cdot\|_*$, and let the loss satisfy Assumption 2 with a subgradient selector measurable in $z$; $\lambda,\epsilon>0$, $K_{\lambda,\epsilon,B}=B/(\lambda\epsilon)$ and $L\ge1$. For every $\theta\in\Theta$ the RT-MLMC estimator (17) satisfies, with all integrands integrable,
--   $$\mathbb E\|v^{RT\text{-}MLMC}(\theta)\|_*^2\le\mathfrak c^{-2}\,\mathbb E\|v^{RT\text{-}MLMC}(\theta)\|_2^2,\qquad
--   \mathbb E\|v^{RT\text{-}MLMC}(\theta)\|_2^2=\sum_{\ell=0}^{L}\frac1{p_\ell}\,\mathbb E\|G^\ell(\theta,\zeta^\ell)\|_2^2,$$
--   $$\sum_{\ell=0}^{L}\frac1{p_\ell}\,\mathbb E\|G^\ell(\theta,\zeta^\ell)\|_2^2\le2(L+1)L_f^2\exp(4K_{\lambda,\epsilon,B}),$$
--   and therefore
--   $$\mathbb E\|v^{RT\text{-}MLMC}(\theta)\|_*^2\le\frac{2(L+1)L_f^2\exp(4K_{\lambda,\epsilon,B})}{\mathfrak c^2}=:(M_*^{RT\text{-}MLMC})^2 .$$
--
--   This is the second-moment constant that, fed into Lemma EC.7, fixes the RT-MLMC iteration count of Theorem 2(II).
--
--   **Formalization Note** The paper's display writes the chain as $\mathbb E\|v\|_*^2\le\mathfrak c^{-2}\mathbb E\|v\|_2^2=\sum_\ell p_\ell^{-1}\mathbb E\|G^\ell\|_2^2\le2(L+1)L_f^2e^{4K}$, dropping the factor $\mathfrak c^{-2}$ after the first inequality; the statement keeps it. The paper's $T$ for RT-MLMC carries $\mathfrak c^2$ in its denominator, which matches only the corrected constant. Both agree when $\mathfrak c=1$.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, App. EC.6.1, RT-MLMC display, p. ec20 (𝔠^{−2} restored)

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_MirrorSetup
import Definitions.Def_SinkhornDRO_BSMD_Objective
import Definitions.Def_SinkhornDRO_BSMD_Estimators

open MeasureTheory ProbabilityTheory

namespace SinkhornDRO.BSMD

/-- App. EC.6.1, RT-MLMC display, p. ec20 (Wang–Gao–Xie, arXiv:2109.11926v5): under Assumption 2,
for every `θ ∈ Θ` the RT-MLMC estimator (17) satisfies
`E‖v‖_*² ≤ 𝔠⁻² E‖v‖₂²`, `E‖v‖₂² = Σ_{ℓ=0}^{L} p_ℓ⁻¹ E‖G^ℓ(θ, ζ^ℓ)‖₂²`,
`Σ_{ℓ=0}^{L} p_ℓ⁻¹ E‖G^ℓ(θ, ζ^ℓ)‖₂² ≤ 2(L+1) L_f² exp(4K_{λ,ε,B})`, and hence
`E‖v‖_*² ≤ 2(L+1) L_f² exp(4K_{λ,ε,B}) / 𝔠²` (the paper's display drops the `𝔠⁻²` after its first
inequality). -/
theorem rtmlmc_second_moment {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (Θ : Set (Param d)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ) (𝒩 : MirrorNorm d)
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (lam eps : ℝ) (hlam : 0 < lam) (heps : 0 < eps)
    (f : Param d → Z → ℝ) (hf_meas : ∀ θ, Measurable (f θ))
    (Lf B : ℝ) (hA2I : Asm2Convex f) (hA2II : Asm2Lipschitz f Lf) (hA2III : Asm2Bounded Θ f B)
    (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg) (hsg_meas : ∀ θ, Measurable (sg θ))
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ θ ∈ Θ,
      Integrable (fun ζ => dualNorm 𝒩 (vRT lam eps f sg L θ ζ) ^ 2) (rtLaw P Q L) ∧
      Integrable (fun ζ => ‖vRT lam eps f sg L θ ζ‖ ^ 2) (rtLaw P Q L) ∧
      ∫ ζ, dualNorm 𝒩 (vRT lam eps f sg L θ ζ) ^ 2 ∂(rtLaw P Q L)
        ≤ (𝒩.c ^ 2)⁻¹ * ∫ ζ, ‖vRT lam eps f sg L θ ζ‖ ^ 2 ∂(rtLaw P Q L) ∧
      ∫ ζ, ‖vRT lam eps f sg L θ ζ‖ ^ 2 ∂(rtLaw P Q L)
        = ∑ ℓ : Fin (L + 1), (levelProb L ℓ)⁻¹ *
            ∫ ζ, ‖levelG lam eps f sg ℓ θ ζ.2‖ ^ 2 ∂(levelLaw P Q (2 ^ (ℓ : ℕ))) ∧
      ∑ ℓ : Fin (L + 1), (levelProb L ℓ)⁻¹ *
            ∫ ζ, ‖levelG lam eps f sg ℓ θ ζ.2‖ ^ 2 ∂(levelLaw P Q (2 ^ (ℓ : ℕ)))
        ≤ 2 * (L + 1) * Lf ^ 2 * Real.exp (4 * (B / (lam * eps))) ∧
      ∫ ζ, dualNorm 𝒩 (vRT lam eps f sg L θ ζ) ^ 2 ∂(rtLaw P Q L)
        ≤ msqRT L Lf (B / (lam * eps)) 𝒩.c := by sorry

end SinkhornDRO.BSMD
