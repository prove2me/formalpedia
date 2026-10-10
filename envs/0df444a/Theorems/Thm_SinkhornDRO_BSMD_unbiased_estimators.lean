-- Prove2me | Theorems.Thm_SinkhornDRO_BSMD_unbiased_estimators
-- name    : SinkhornDRO.BSMD.unbiased_estimators
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:26:02.682989+00:00
-- url     : https://prove2.me/theorems/a8238122-51f6-47f1-bac0-de4ca84760fe
-- title:
--   §4.1.1, p. 15 — g^ℓ is unbiased for a subgradient of F^ℓ, G^ℓ for the level difference, and E v^{RT-MLMC} = E v^{SG}
-- statement:
--   Let $\Theta\subseteq\mathbb R^{d_\theta}$ be closed and convex, $\lambda,\epsilon>0$, and let the loss $f_\theta(z)$ (measurable in $z$) satisfy Assumption 2 with a subgradient selector $\nabla_\theta f_\theta(z)$ measurable in $z$. Let $F^\ell$ be the level-$\ell$ approximation (14), and $g^\ell$, $G^\ell$, $v^{SG}$, $v^{RT\text{-}MLMC}$ the estimators of (15)–(17), each expectation taken over the corresponding sampling law. Then:
--
--   1. for every level $\ell$ and $\theta\in\Theta$, $g^\ell(\theta,\zeta^\ell)$ is integrable and its mean is a subgradient of $F^\ell$ at $\theta$ relative to $\Theta$:
--   $$F^\ell(\theta)+\big\langle\mathbb E[g^\ell(\theta,\zeta^\ell)],\theta'-\theta\big\rangle\le F^\ell(\theta')\qquad(\theta'\in\Theta);$$
--   2. for $\theta\in\Theta$, $\mathbb E[G^0(\theta,\zeta^0)]=\mathbb E[g^0(\theta,\zeta^0)]$ and
--   $$\mathbb E[G^{\ell+1}(\theta,\zeta^{\ell+1})]=\mathbb E[g^{\ell+1}(\theta,\zeta^{\ell+1})]-\mathbb E[g^{\ell}(\theta,\zeta^{\ell})];$$
--   3. for every $L\ge1$ and $\theta\in\Theta$, $v^{RT\text{-}MLMC}(\theta)$ is integrable and
--   $$\mathbb E[v^{RT\text{-}MLMC}(\theta)]=\mathbb E[g^L(\theta,\zeta^L)]=\mathbb E[v^{SG}(\theta)].$$
--
--   This is the paper's claim that $g^\ell$ is an unbiased estimator of $\nabla_\theta F^\ell(\theta)$ and $G^\ell$ an unbiased estimator of $\nabla_\theta F^\ell(\theta)-\nabla_\theta F^{\ell-1}(\theta)$; it makes both estimators unbiased for a subgradient of $F^L$, which is the hypothesis of Lemma EC.7.
--
--   **Formalization Note** For a nonsmooth loss $\nabla_\theta F^\ell$ is a subgradient, not a gradient, so "$G^\ell$ is unbiased for $\nabla F^\ell-\nabla F^{\ell-1}$" is read as part 2: the mean of $G^\ell$ is the difference of the means of $g^\ell$ and $g^{\ell-1}$ (each of which is a subgradient by part 1), with $F^{-1}:=0$, $G^0=g^0$. Part 3 is the telescoping consequence that the paper uses.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, §4.1.1, p. 15 (prose claim after the definitions of g^ℓ, G^ℓ); (17), p. 16

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_Objective
import Definitions.Def_SinkhornDRO_BSMD_Estimators

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace SinkhornDRO.BSMD

/-- §4.1.1, p. 15 (Wang–Gao–Xie, arXiv:2109.11926v5): "`g^ℓ(θ, ζ^ℓ)` is an unbiased estimator of
`∇_θF^ℓ(θ)`, while `G^ℓ(θ, ζ^ℓ)` is an unbiased estimator of `∇_θF^ℓ(θ) − ∇_θF^{ℓ−1}(θ)`",
in its nonsmooth reading, under Assumption 2:
1. for every level `ℓ` and `θ ∈ Θ`, `E[g^ℓ(θ, ζ^ℓ)]` is a subgradient of `F^ℓ` at `θ` relative to
   `Θ`;
2. `E[G^0] = E[g^0]` and `E[G^{ℓ+1}] = E[g^{ℓ+1}] − E[g^ℓ]` (each expectation under its own
   level's sampling law), so `G^ℓ` estimates the difference of the selected subgradients of `F^ℓ`
   and `F^{ℓ−1}`;
3. consequently the RT-MLMC estimator has the same mean as the SG estimator:
   `E[v^{RT-MLMC}(θ)] = E[g^L(θ, ζ^L)] = E[v^{SG}(θ)]`. -/
theorem unbiased_estimators {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (Θ : Set (Param d)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (lam eps : ℝ) (hlam : 0 < lam) (heps : 0 < eps)
    (f : Param d → Z → ℝ) (hf_meas : ∀ θ, Measurable (f θ))
    (Lf B : ℝ) (hA2I : Asm2Convex f) (hA2II : Asm2Lipschitz f Lf) (hA2III : Asm2Bounded Θ f B)
    (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg) (hsg_meas : ∀ θ, Measurable (sg θ)) :
    (∀ (ℓ : ℕ), ∀ θ ∈ Θ,
      Integrable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) => levelg lam eps f sg ℓ θ ζ.2)
          (levelLaw P Q (2 ^ ℓ)) ∧
        ∀ θ' ∈ Θ, objFℓ P Q lam eps f ℓ θ +
            ⟪∫ ζ, levelg lam eps f sg ℓ θ ζ.2 ∂(levelLaw P Q (2 ^ ℓ)), θ' - θ⟫
          ≤ objFℓ P Q lam eps f ℓ θ') ∧
    (∀ θ ∈ Θ,
      ∫ ζ, levelG lam eps f sg 0 θ ζ.2 ∂(levelLaw P Q (2 ^ 0))
        = ∫ ζ, levelg lam eps f sg 0 θ ζ.2 ∂(levelLaw P Q (2 ^ 0))) ∧
    (∀ (ℓ : ℕ), ∀ θ ∈ Θ,
      ∫ ζ, levelG lam eps f sg (ℓ + 1) θ ζ.2 ∂(levelLaw P Q (2 ^ (ℓ + 1)))
        = ∫ ζ, levelg lam eps f sg (ℓ + 1) θ ζ.2 ∂(levelLaw P Q (2 ^ (ℓ + 1)))
          - ∫ ζ, levelg lam eps f sg ℓ θ ζ.2 ∂(levelLaw P Q (2 ^ ℓ))) ∧
    (∀ (L : ℕ), 1 ≤ L → ∀ θ ∈ Θ,
      Integrable (vRT lam eps f sg L θ) (rtLaw P Q L) ∧
        ∫ ζ, vRT lam eps f sg L θ ζ ∂(rtLaw P Q L)
          = ∫ ζ, vSG lam eps f sg L θ ζ ∂(levelLaw P Q (2 ^ L))) := by sorry

end SinkhornDRO.BSMD
