-- Prove2me | Theorems.Thm_SinkhornDRO_BSMD_lemma_EC_6_I
-- name    : SinkhornDRO.BSMD.lemma_EC_6_I
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:24:55.442433+00:00
-- url     : https://prove2.me/theorems/09f63fc9-e0a6-43f3-9d10-b0a5d976dda4
-- title:
--   Lemma EC.6 (I) — |F^ℓ(θ) − F(θ)| ≤ λε exp(2B/(λε)) 2^{−(ℓ+1)} on Θ
-- statement:
--   Let $\lambda,\epsilon>0$, let $\widehat{\mathbb P}$ be a probability measure and $x\mapsto\mathbb Q_x$ a Markov kernel on $\mathcal Z$, and let the loss $f_\theta(z)$ be measurable in $z$ and satisfy Assumption 2(III): $0\le f_\theta(z)\le B$ for $\theta\in\Theta$. Put $K_{\lambda,\epsilon,B}=B/(\lambda\epsilon)$. Then for every level $\ell\in\mathbb N$,
--   $$\big|F^\ell(\theta)-F(\theta)\big|\le\lambda\epsilon\,\exp(2K_{\lambda,\epsilon,B})\cdot2^{-(\ell+1)}\qquad\forall\theta\in\Theta,$$
--   where $F$ is the objective (11) and $F^\ell$ its level-$\ell$ approximation (14).
--
--   The bound controls the bias $\Delta_F$ of Lemma EC.7 when BSMD runs on subgradients of $F^L$ in place of $F$.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. ec18, Lemma EC.6 (I)

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_Objective

open MeasureTheory ProbabilityTheory

namespace SinkhornDRO.BSMD

/-- Lemma EC.6 (I) (Wang–Gao–Xie, arXiv:2109.11926v5, p. ec18): under Assumption 2(III),
`|F^ℓ(θ) − F(θ)| ≤ λε exp(2K_{λ,ε,B}) · 2^{−(ℓ+1)}` for every `θ ∈ Θ`, where `K_{λ,ε,B} = B/(λε)`. -/
theorem lemma_EC_6_I {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (Θ : Set (Param d)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (lam eps : ℝ) (hlam : 0 < lam) (heps : 0 < eps)
    (f : Param d → Z → ℝ) (hf_meas : ∀ θ, Measurable (f θ))
    (B : ℝ) (hA2III : Asm2Bounded Θ f B) (ℓ : ℕ) :
    ∀ θ ∈ Θ, |objFℓ P Q lam eps f ℓ θ - objF P Q lam eps f θ|
      ≤ lam * eps * Real.exp (2 * (B / (lam * eps))) * ((2 : ℝ) ^ (ℓ + 1))⁻¹ := by sorry

end SinkhornDRO.BSMD
