-- Prove2me | Theorems.Thm_SinkhornDRO_BSMD_lemma_EC_6_III_b
-- name    : SinkhornDRO.BSMD.lemma_EC_6_III_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:26:57.688974+00:00
-- url     : https://prove2.me/theorems/b418880b-9f7c-4680-8df8-b54a3d4b04e4
-- title:
--   Lemma EC.6 (III), second part — E‖G^ℓ(θ, ζ^ℓ)‖₂² ≤ L_f² exp(4B/(λε)) 2^{−ℓ} on Θ
-- statement:
--   In the setting of Lemma EC.6 (III), assume in addition Assumption 2(III), $0\le f_\theta(z)\le B$ for $\theta\in\Theta$, and put $K_{\lambda,\epsilon,B}=B/(\lambda\epsilon)$. Then for every level $\ell$,
--   $$\mathbb E\big[\|G^\ell(\theta,\zeta^\ell)\|_2^2\big]\le L_f^2\exp(4K_{\lambda,\epsilon,B})\cdot2^{-\ell}\qquad\forall\theta\in\Theta,$$
--   and the integrand is integrable. Here $G^\ell=\nabla_\theta A^\ell$ is computed with the same selected subgradients $\nabla_\theta f_\theta(z_j)$ in its three blocks, as (17) prescribes.
--
--   The geometric decay in $\ell$ is what makes the RT-MLMC estimator's second moment grow only linearly in $L$.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. ec19, Lemma EC.6 (III), second display

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_Objective
import Definitions.Def_SinkhornDRO_BSMD_Estimators

open MeasureTheory ProbabilityTheory

namespace SinkhornDRO.BSMD

/-- Lemma EC.6 (III), second part (Wang–Gao–Xie, arXiv:2109.11926v5, p. ec19): under
Assumption 2(II) and 2(III),
`E[‖G^ℓ(θ, ζ^ℓ)‖₂²] ≤ L_f² exp(4K_{λ,ε,B}) · 2^{−ℓ}` for every `θ ∈ Θ`, `K_{λ,ε,B} = B/(λε)`,
where `G^ℓ = ∇_θ A^ℓ` is computed with the same subgradients `sg θ z_j` in all three blocks. -/
theorem lemma_EC_6_III_b {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (Θ : Set (Param d)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (lam eps : ℝ) (hlam : 0 < lam) (heps : 0 < eps)
    (f : Param d → Z → ℝ) (hf_meas : ∀ θ, Measurable (f θ))
    (Lf B : ℝ) (hA2I : Asm2Convex f) (hA2II : Asm2Lipschitz f Lf) (hA2III : Asm2Bounded Θ f B)
    (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg) (hsg_meas : ∀ θ, Measurable (sg θ))
    (ℓ : ℕ) :
    ∀ θ ∈ Θ,
      Integrable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) => ‖levelG lam eps f sg ℓ θ ζ.2‖ ^ 2)
          (levelLaw P Q (2 ^ ℓ)) ∧
        ∫ ζ, ‖levelG lam eps f sg ℓ θ ζ.2‖ ^ 2 ∂(levelLaw P Q (2 ^ ℓ))
          ≤ Lf ^ 2 * Real.exp (4 * (B / (lam * eps))) * ((2 : ℝ) ^ ℓ)⁻¹ := by sorry

end SinkhornDRO.BSMD
